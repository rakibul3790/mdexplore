#!/usr/bin/env bash
set -Eeuo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VENV_DIR="${SCRIPT_DIR}/.venv"
REQUIREMENTS_FILE="${SCRIPT_DIR}/requirements.txt"
APP_FILE="${SCRIPT_DIR}/mdexplore.py"
REQ_HASH_FILE="${VENV_DIR}/.requirements.sha256"
LOG_DIR="${XDG_CACHE_HOME:-${HOME}/.cache}/mdexplore"
LOG_FILE="${LOG_DIR}/launcher.log"
MAX_LOG_LINES=1000
NON_INTERACTIVE=0

trim_log_file() {
  local file_path="$1"
  local max_lines="$2"
  local tmp_file=""
  if [[ ! -f "${file_path}" ]]; then
    return 0
  fi

  local line_count
  line_count="$(wc -l < "${file_path}")"
  if [[ "${line_count}" -le "${max_lines}" ]]; then
    return 0
  fi

  tmp_file="${file_path}.tmp.$$"
  if tail -n "${max_lines}" "${file_path}" > "${tmp_file}"; then
    mv "${tmp_file}" "${file_path}"
  else
    rm -f "${tmp_file}"
  fi
}

trim_log_file_inplace() {
  local file_path="$1"
  local max_lines="$2"
  local tmp_file=""
  if [[ ! -f "${file_path}" ]]; then
    return 0
  fi

  local line_count
  line_count="$(wc -l < "${file_path}")"
  if [[ "${line_count}" -le "${max_lines}" ]]; then
    return 0
  fi

  tmp_file="${file_path}.tmp.$$"
  if tail -n "${max_lines}" "${file_path}" > "${tmp_file}"; then
    : > "${file_path}"
    cat "${tmp_file}" >> "${file_path}"
    rm -f "${tmp_file}"
  else
    rm -f "${tmp_file}"
  fi
}

if [[ ! -t 1 ]]; then
  NON_INTERACTIVE=1
  mkdir -p "${LOG_DIR}" 2>/dev/null || true
  trim_log_file "${LOG_FILE}" "${MAX_LOG_LINES}"
  exec >> "${LOG_FILE}" 2>&1
fi

notify_failure() {
  local message="$1"
  if [[ "${NON_INTERACTIVE}" -eq 1 ]] && command -v notify-send >/dev/null 2>&1; then
    notify-send "mdexplore launcher failed" "${message}" || true
  fi
}

on_error() {
  local exit_code="$1"
  local line_no="$2"
  local message="Exit ${exit_code} at line ${line_no}. See ${LOG_FILE}"
  echo "ERROR: ${message}"
  if [[ "${NON_INTERACTIVE}" -eq 1 ]]; then
    trim_log_file_inplace "${LOG_FILE}" "${MAX_LOG_LINES}"
  fi
  notify_failure "${message}"
}

trap 'on_error "$?" "$LINENO"' ERR
echo "[$(date +'%Y-%m-%d %H:%M:%S')] mdexplore.sh start args: $*"
if [[ "${NON_INTERACTIVE}" -eq 1 ]]; then
  trim_log_file_inplace "${LOG_FILE}" "${MAX_LOG_LINES}"
fi

usage() {
  echo "Usage: $(basename "$0") [--mermaid-backend js|rust] [PATH]"
  echo "If PATH is omitted, mdexplore uses ~/.mdexplore.cfg or HOME."
}

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  usage
  exit 0
fi

if ! command -v python3 >/dev/null 2>&1; then
  echo "python3 is required but was not found in PATH." >&2
  exit 1
fi

decode_file_uri() {
  local uri="$1"
  python3 - "$uri" <<'PY'
import sys
from urllib.parse import unquote, urlparse

uri = sys.argv[1]
parsed = urlparse(uri)
if parsed.scheme != "file":
    print(uri)
    raise SystemExit(0)

path = unquote(parsed.path or "")
if parsed.netloc and parsed.netloc not in ("", "localhost"):
    path = f"//{parsed.netloc}{path}"
print(path)
PY
}

resolve_local_script_path() {
  local candidate=""
  for candidate in "$@"; do
    [[ -z "${candidate}" ]] && continue
    if [[ -f "${candidate}" ]]; then
      printf '%s\n' "${candidate}"
      return 0
    fi
  done
  return 1
}

configure_local_renderer_overrides() {
  local detected_path=""

  if [[ -z "${MDEXPLORE_MATHJAX_JS:-}" ]]; then
    detected_path="$(resolve_local_script_path \
      "${SCRIPT_DIR}/mathjax/es5/tex-svg.js" \
      "${SCRIPT_DIR}/mathjax/tex-svg.js" \
      "${SCRIPT_DIR}/assets/mathjax/es5/tex-svg.js" \
      "${SCRIPT_DIR}/vendor/mathjax/es5/tex-svg.js" \
      "/usr/share/javascript/mathjax/es5/tex-svg.js" \
      "/usr/share/mathjax/es5/tex-svg.js" \
      "/usr/share/nodejs/mathjax/es5/tex-svg.js" \
      "${SCRIPT_DIR}/mathjax/es5/tex-mml-chtml.js" \
      "${SCRIPT_DIR}/mathjax/tex-mml-chtml.js" \
      "${SCRIPT_DIR}/assets/mathjax/es5/tex-mml-chtml.js" \
      "${SCRIPT_DIR}/vendor/mathjax/es5/tex-mml-chtml.js" \
      "/usr/share/javascript/mathjax/es5/tex-mml-chtml.js" \
      "/usr/share/mathjax/es5/tex-mml-chtml.js" \
      "/usr/share/nodejs/mathjax/es5/tex-mml-chtml.js" \
      || true)"
    if [[ -n "${detected_path}" ]]; then
      export MDEXPLORE_MATHJAX_JS="${detected_path}"
      echo "Using local MathJax bundle: ${MDEXPLORE_MATHJAX_JS}"
    fi
  else
    echo "Using configured MDEXPLORE_MATHJAX_JS: ${MDEXPLORE_MATHJAX_JS}"
  fi

  if [[ -z "${MDEXPLORE_MERMAID_JS:-}" ]]; then
    detected_path="$(resolve_local_script_path \
      "${SCRIPT_DIR}/mermaid/mermaid.min.js" \
      "${SCRIPT_DIR}/mermaid/dist/mermaid.min.js" \
      "${SCRIPT_DIR}/assets/mermaid/mermaid.min.js" \
      "${SCRIPT_DIR}/assets/mermaid/dist/mermaid.min.js" \
      "${SCRIPT_DIR}/vendor/mermaid/mermaid.min.js" \
      "${SCRIPT_DIR}/vendor/mermaid/dist/mermaid.min.js" \
      "/usr/share/javascript/mermaid/mermaid.min.js" \
      "/usr/share/nodejs/mermaid/dist/mermaid.min.js" \
      || true)"
    if [[ -n "${detected_path}" ]]; then
      export MDEXPLORE_MERMAID_JS="${detected_path}"
      echo "Using local Mermaid bundle: ${MDEXPLORE_MERMAID_JS}"
    fi
  else
    echo "Using configured MDEXPLORE_MERMAID_JS: ${MDEXPLORE_MERMAID_JS}"
  fi
}

configure_mermaid_rs_override() {
  local detected_path=""

  if [[ -z "${MDEXPLORE_MERMAID_RS_BIN:-}" ]]; then
    detected_path="$(resolve_local_script_path \
      "${HOME}/.cargo/bin/mmdr" \
      "${SCRIPT_DIR}/vendor/mermaid-rs-renderer/target/release/mmdr" \
      "${SCRIPT_DIR}/vendor/mermaid-rs-renderer/mmdr" \
      "${SCRIPT_DIR}/vendor/mermaid-rs-renderer/bin/mmdr" \
      "${SCRIPT_DIR}/mermaid-rs-renderer/target/release/mmdr" \
      "${SCRIPT_DIR}/mmdr" \
      || true)"
    if [[ -n "${detected_path}" ]]; then
      export MDEXPLORE_MERMAID_RS_BIN="${detected_path}"
      echo "Using local Mermaid Rust renderer: ${MDEXPLORE_MERMAID_RS_BIN}"
    fi
  else
    echo "Using configured MDEXPLORE_MERMAID_RS_BIN: ${MDEXPLORE_MERMAID_RS_BIN}"
  fi
}

configure_qt_graphics_fallback() {
  # Some desktop/driver combinations fail to create an OpenGL context for
  # QtWebEngine. Apply software settings only in fallback mode.
  if [[ -z "${QT_QUICK_BACKEND:-}" ]]; then
    export QT_QUICK_BACKEND="software"
    echo "Using QT_QUICK_BACKEND=software"
  fi
  if [[ -z "${QSG_RHI_BACKEND:-}" ]]; then
    export QSG_RHI_BACKEND="software"
    echo "Using QSG_RHI_BACKEND=software"
  fi
  if [[ -z "${QT_OPENGL:-}" ]]; then
    export QT_OPENGL="software"
    echo "Using QT_OPENGL=software"
  fi

  # Keep any user-provided Chromium flags and append GPU disable only if absent.
  local chromium_flags="${QTWEBENGINE_CHROMIUM_FLAGS:-}"
  if [[ " ${chromium_flags} " != *" --disable-gpu "* ]]; then
    chromium_flags="${chromium_flags} --disable-gpu"
    chromium_flags="${chromium_flags#"${chromium_flags%%[![:space:]]*}"}"
    chromium_flags="${chromium_flags%"${chromium_flags##*[![:space:]]}"}"
    export QTWEBENGINE_CHROMIUM_FLAGS="${chromium_flags}"
    echo "Using QTWEBENGINE_CHROMIUM_FLAGS=${QTWEBENGINE_CHROMIUM_FLAGS}"
  fi
}

TARGET_PATH=""
APP_ARGS=()
MERMAID_BACKEND_EXPLICIT=0
while [[ $# -gt 0 ]]; do
  RAW_ARG="$1"
  shift
  [[ -z "${RAW_ARG}" ]] && continue

  case "${RAW_ARG}" in
    ""|"%u"|"%U"|"%f"|"%F")
      continue
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    --mermaid-backend)
      if [[ $# -eq 0 ]]; then
        echo "Missing value for --mermaid-backend (expected js|rust)." >&2
        exit 1
      fi
      APP_ARGS+=("${RAW_ARG}" "$1")
      MERMAID_BACKEND_EXPLICIT=1
      shift
      continue
      ;;
    --mermaid-backend=*)
      APP_ARGS+=("${RAW_ARG}")
      MERMAID_BACKEND_EXPLICIT=1
      continue
      ;;
  esac

  URI_INPUT=0
  CANDIDATE_PATH=""
  case "${RAW_ARG}" in
    -*)
      # Some desktop launchers may add non-path args. Ignore them.
      echo "Ignoring non-path argument: ${RAW_ARG}"
      continue
      ;;
    file://*)
      URI_INPUT=1
      CANDIDATE_PATH="$(decode_file_uri "${RAW_ARG}")"
      ;;
    *)
      CANDIDATE_PATH="${RAW_ARG}"
      ;;
  esac

  if [[ -f "${CANDIDATE_PATH}" ]]; then
    CANDIDATE_PATH="$(dirname "${CANDIDATE_PATH}")"
  fi

  if [[ -d "${CANDIDATE_PATH}" ]]; then
    TARGET_PATH="${CANDIDATE_PATH}"
    continue
  fi

  if [[ "${URI_INPUT}" -eq 1 ]]; then
    # Desktop URI launches can occasionally pass odd values. Fall back
    # to default root instead of aborting a dock/menu launch.
    echo "Ignoring invalid URI-derived path: ${CANDIDATE_PATH}"
    continue
  fi

  if [[ -n "${CANDIDATE_PATH}" ]]; then
    echo "Ignoring invalid path argument: ${CANDIDATE_PATH}"
  fi
done

if [[ -z "${DISPLAY:-}" && -z "${WAYLAND_DISPLAY:-}" ]]; then
  echo "No GUI display detected (DISPLAY/WAYLAND_DISPLAY unset)." >&2
  echo "Run this from a desktop session with GUI access." >&2
  if [[ "${NON_INTERACTIVE}" -eq 1 ]]; then
    trim_log_file_inplace "${LOG_FILE}" "${MAX_LOG_LINES}"
  fi
  exit 1
fi

needs_install=0
if [[ ! -d "${VENV_DIR}" ]]; then
  echo "Creating virtual environment at ${VENV_DIR}..."
  python3 -m venv "${VENV_DIR}"
  needs_install=1
fi

VENV_PYTHON="${VENV_DIR}/bin/python"
if [[ ! -x "${VENV_PYTHON}" ]]; then
  echo "Virtual environment python not found: ${VENV_PYTHON}" >&2
  exit 1
fi

runtime_import_check() {
  "${VENV_PYTHON}" - <<'PY'
import importlib

required = [
    "markdown_it",
    "mdit_py_plugins.dollarmath",
    "linkify_it",
    "PySide6.QtWebEngineWidgets",
    "pypdf",
    "reportlab.pdfgen.canvas",
]

missing = []
for module_name in required:
    try:
        importlib.import_module(module_name)
    except Exception as exc:
        missing.append(f"{module_name}: {exc}")

if missing:
    print("Runtime dependency check failed:")
    for item in missing:
        print(f"  - {item}")
    raise SystemExit(1)
PY
}

current_hash="$(sha256sum "${REQUIREMENTS_FILE}" | awk '{print $1}')"
stored_hash=""
if [[ -f "${REQ_HASH_FILE}" ]]; then
  stored_hash="$(cat "${REQ_HASH_FILE}")"
fi

if [[ "${needs_install}" -eq 1 || "${current_hash}" != "${stored_hash}" ]]; then
  echo "Installing Python dependencies..."
  "${VENV_PYTHON}" -m pip install --disable-pip-version-check -r "${REQUIREMENTS_FILE}"
  printf '%s\n' "${current_hash}" > "${REQ_HASH_FILE}"
else
  echo "Dependencies already up to date."
fi

if ! runtime_import_check; then
  echo "Detected incomplete Python runtime. Reinstalling dependencies..."
  "${VENV_PYTHON}" -m pip install --disable-pip-version-check --upgrade --force-reinstall -r "${REQUIREMENTS_FILE}"
  printf '%s\n' "${current_hash}" > "${REQ_HASH_FILE}"
  runtime_import_check
fi

configure_local_renderer_overrides
configure_mermaid_rs_override

# Default to Rust Mermaid renderer for launcher-driven debugging, unless the
# caller explicitly selected a backend on the command line.
if [[ "${MERMAID_BACKEND_EXPLICIT}" -eq 0 ]]; then
  APP_ARGS+=("--mermaid-backend" "rust")
  echo "Defaulting Mermaid backend to rust (override with --mermaid-backend js)."
fi

if [[ "${NON_INTERACTIVE}" -eq 1 ]]; then
  trim_log_file_inplace "${LOG_FILE}" "${MAX_LOG_LINES}"
fi

launch_mdexplore() {
  # Do not override argv[0] for python; it can break venv detection and
  # cause imports to resolve against system packages.
  if [[ -n "${TARGET_PATH}" ]]; then
    echo "Launching mdexplore for: ${TARGET_PATH}"
    "${VENV_PYTHON}" "${APP_FILE}" "${APP_ARGS[@]}" "${TARGET_PATH}"
  else
    echo "Launching mdexplore using configured default root (or home)"
    "${VENV_PYTHON}" "${APP_FILE}" "${APP_ARGS[@]}"
  fi
}

# Prefer GPU on first launch, then retry once with software rendering fallback.
if launch_mdexplore; then
  exit 0
fi

echo "Initial launch failed; retrying with software rendering fallback..."
configure_qt_graphics_fallback
launch_mdexplore
