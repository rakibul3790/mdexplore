#!/usr/bin/env python3
"""mdexplore: fast markdown browser/editor launcher for Ubuntu."""

from __future__ import annotations

import argparse
import base64
from bisect import bisect_right
import html
import hashlib
from io import BytesIO
import json
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import xml.etree.ElementTree as ET
from collections import deque
from difflib import SequenceMatcher
from pathlib import Path

from markdown_it import MarkdownIt
from mdit_py_plugins.dollarmath import dollarmath_plugin
from PySide6.QtCore import QDir, QEventLoop, QMarginsF, QMimeData, QObject, QPoint, QRunnable, QSize, Qt, QThreadPool, QTimer, QUrl, Signal
from PySide6.QtGui import QAction, QBrush, QClipboard, QColor, QFont, QIcon, QImage, QOffscreenSurface, QOpenGLContext, QPainter, QPageLayout, QPageSize, QPalette, QPen, QPixmap, QPolygon, QSurfaceFormat
from PySide6.QtSvg import QSvgRenderer
from PySide6.QtWebEngineCore import QWebEngineSettings
from PySide6.QtWebEngineWidgets import QWebEngineView
from PySide6.QtWidgets import (
    QApplication,
    QFileSystemModel,
    QHBoxLayout,
    QInputDialog,
    QLabel,
    QLineEdit,
    QMainWindow,
    QMenu,
    QMessageBox,
    QPushButton,
    QSizePolicy,
    QSplitter,
    QStyle,
    QStyledItemDelegate,
    QStyleOptionViewItem,
    QTabBar,
    QTreeView,
    QVBoxLayout,
    QWidget,
)

# Core runtime and document-behavior knobs live together here so PDF/layout
# tuning does not end up scattered through the code or embedded JS.
CONFIG_FILE_NAME = ".mdexplore.cfg"
SEARCH_CLOSE_WORD_GAP = 50
PDF_EXPORT_PRECHECK_MAX_ATTEMPTS = 60
PDF_EXPORT_PRECHECK_INTERVAL_MS = 140
MERMAID_CACHE_JSON_TOKEN = "__MDEXPLORE_MERMAID_CACHE_JSON__"
DIAGRAM_VIEW_STATE_JSON_TOKEN = "__MDEXPLORE_DIAGRAM_VIEW_STATE_JSON__"
MERMAID_SVG_CACHE_MAX_ENTRIES = 256
MERMAID_SVG_MAX_CHARS = 250_000
PLANTUML_RESTORE_BATCH_SIZE = 2
MERMAID_CACHE_RESTORE_BATCH_SIZE = 2
RESTORE_OVERLAY_TIMEOUT_SECONDS = 25.0
RESTORE_OVERLAY_SHOW_DELAY_MS = 350
RESTORE_OVERLAY_MAX_VISIBLE_SECONDS = 1.0
MERMAID_BACKEND_JS = "js"
MERMAID_BACKEND_RUST = "rust"
# PDF print layout may shrink diagrams to keep them on one page. If the
# resulting largest diagram font would fall below this floor, the diagram is
# allowed to spill across pages instead. Lower this only if a smaller single-
# page rendering is preferable to a multi-page spill.
MIN_PRINT_DIAGRAM_FONT_PT = 3 # 2.4
# The corresponding upper cap for print scaling. Diagrams may be shrunk more,
# but they should never be enlarged beyond roughly this text size.
MAX_PRINT_DIAGRAM_FONT_PT = 12.0
# Vertical breathing room reserved between a heading cluster and its diagram.
PDF_PRINT_HEADING_TO_DIAGRAM_GAP_PX = 16
# Additional safety buffer left on the page so borderline fits do not clip when
# Chromium computes the final print flow.
PDF_PRINT_LAYOUT_SAFETY_PX = 40
# Lower bound for the diagram area that is considered worth trying to keep on a
# single page before immediately falling back to spill mode.
PDF_PRINT_KEEP_MIN_HEIGHT_PX = 120
# Letter page size expressed in CSS pixels for Chromium print layout math.
PDF_PRINT_PORTRAIT_LETTER_WIDTH_PX = 1000 # 816
PDF_PRINT_PORTRAIT_LETTER_HEIGHT_PX = 1310 # 1056
PDF_PRINT_LANDSCAPE_LETTER_WIDTH_PX = 1100 # 1056
PDF_PRINT_LANDSCAPE_LETTER_HEIGHT_PX = 860 # 816
# Effective horizontal/vertical print margins removed from the page-size budget
# when deciding whether a diagram can fit in portrait or landscape.
PDF_PRINT_HORIZONTAL_MARGIN_PX = 80 # 96
PDF_PRINT_VERTICAL_MARGIN_PX = 130 # 140
# Floor values keep printable dimensions sane if the margin calculation would
# otherwise leave an unrealistically small viewport for fit heuristics.
PDF_PRINT_PORTRAIT_MIN_WIDTH_PX = 320 # 320
PDF_PRINT_PORTRAIT_MIN_HEIGHT_PX = 320 # 320
PDF_PRINT_LANDSCAPE_MIN_WIDTH_PX = 360 # 360
PDF_PRINT_LANDSCAPE_MIN_HEIGHT_PX = 260 # 260
# Wide diagrams become landscape candidates only when their aspect ratio and
# expected width gain clear these thresholds.
PDF_PRINT_WIDE_DIAGRAM_ASPECT_RATIO = 1.19 # 1.25
PDF_PRINT_WIDE_DIAGRAM_LANDSCAPE_GAIN = 1.06 # 1.08
# PlantUML tends to benefit from landscape a bit earlier than Mermaid, so it
# has its own aspect-ratio threshold.
PDF_PRINT_PLANTUML_LANDSCAPE_ASPECT_RATIO = 1.18 # 1.18
# QWebEngineView.setHtml uses an internal data URL path with practical size
# limits; large inline-SVG documents can fail to load. Use file-based loading
# above this threshold.
PREVIEW_SETHTML_MAX_BYTES = 650_000


def _config_file_path() -> Path:
    return Path.home() / CONFIG_FILE_NAME


def _letter_pdf_page_layout() -> QPageLayout:
    """Fallback US Letter layout for callers that need an explicit page geometry."""
    return QPageLayout(
        QPageSize(QPageSize.PageSizeId.Letter),
        QPageLayout.Orientation.Portrait,
        QMarginsF(0.0, 0.0, 0.0, 0.0),
    )


def _configure_qt_graphics_fallback() -> None:
    """Force software rendering env vars for fallback launch paths."""
    if not os.environ.get("QT_QUICK_BACKEND"):
        os.environ["QT_QUICK_BACKEND"] = "software"
    if not os.environ.get("QSG_RHI_BACKEND"):
        os.environ["QSG_RHI_BACKEND"] = "software"
    if not os.environ.get("QT_OPENGL"):
        os.environ["QT_OPENGL"] = "software"
    chromium_flags = os.environ.get("QTWEBENGINE_CHROMIUM_FLAGS", "")
    if "--disable-gpu" not in chromium_flags.split():
        os.environ["QTWEBENGINE_CHROMIUM_FLAGS"] = f"{chromium_flags} --disable-gpu".strip()


def _gpu_context_available() -> bool:
    """Return whether a usable GPU OpenGL context can be created."""
    qt_quick_backend = os.environ.get("QT_QUICK_BACKEND", "").strip().lower()
    qsg_rhi_backend = os.environ.get("QSG_RHI_BACKEND", "").strip().lower()
    qt_opengl = os.environ.get("QT_OPENGL", "").strip().lower()
    chromium_flags = os.environ.get("QTWEBENGINE_CHROMIUM_FLAGS", "").split()

    if qt_quick_backend == "software" or qsg_rhi_backend == "software" or qt_opengl == "software":
        return False
    if "--disable-gpu" in chromium_flags:
        return False

    try:
        surface = QOffscreenSurface()
        surface.setFormat(QSurfaceFormat.defaultFormat())
        surface.create()
        if not surface.isValid():
            return False

        context = QOpenGLContext()
        context.setFormat(surface.format())
        if not context.create():
            return False
        if not context.makeCurrent(surface):
            return False
        context.doneCurrent()
        return True
    except Exception:
        return False


def _pdf_print_layout_knobs() -> dict[str, float | int]:
    """Expose PDF print-layout policy knobs to the in-page preflight JS.

    The hidden QWebEngine preview performs the final pagination classification
    because only the DOM knows the rendered heading heights and intrinsic SVG
    geometry. Keeping the knobs here ensures that policy changes stay in Python
    instead of drifting into anonymous literals inside the embedded template.
    """
    return {
        "headingToDiagramGapPx": PDF_PRINT_HEADING_TO_DIAGRAM_GAP_PX,
        "layoutSafetyPx": PDF_PRINT_LAYOUT_SAFETY_PX,
        "keepMinHeightPx": PDF_PRINT_KEEP_MIN_HEIGHT_PX,
        "minPrintDiagramFontPt": MIN_PRINT_DIAGRAM_FONT_PT,
        "maxPrintDiagramFontPt": MAX_PRINT_DIAGRAM_FONT_PT,
        "portraitLetterWidthPx": PDF_PRINT_PORTRAIT_LETTER_WIDTH_PX,
        "portraitLetterHeightPx": PDF_PRINT_PORTRAIT_LETTER_HEIGHT_PX,
        "landscapeLetterWidthPx": PDF_PRINT_LANDSCAPE_LETTER_WIDTH_PX,
        "landscapeLetterHeightPx": PDF_PRINT_LANDSCAPE_LETTER_HEIGHT_PX,
        "horizontalMarginPx": PDF_PRINT_HORIZONTAL_MARGIN_PX,
        "verticalMarginPx": PDF_PRINT_VERTICAL_MARGIN_PX,
        "portraitMinWidthPx": PDF_PRINT_PORTRAIT_MIN_WIDTH_PX,
        "portraitMinHeightPx": PDF_PRINT_PORTRAIT_MIN_HEIGHT_PX,
        "landscapeMinWidthPx": PDF_PRINT_LANDSCAPE_MIN_WIDTH_PX,
        "landscapeMinHeightPx": PDF_PRINT_LANDSCAPE_MIN_HEIGHT_PX,
        "wideDiagramAspectRatio": PDF_PRINT_WIDE_DIAGRAM_ASPECT_RATIO,
        "wideDiagramLandscapeGain": PDF_PRINT_WIDE_DIAGRAM_LANDSCAPE_GAIN,
        "plantumlLandscapeAspectRatio": PDF_PRINT_PLANTUML_LANDSCAPE_ASPECT_RATIO,
    }


def _load_default_root_from_config() -> Path:
    """Resolve default root when no CLI path is provided."""
    fallback = Path.home()
    cfg_path = _config_file_path()
    try:
        if not cfg_path.exists():
            return fallback
        raw = cfg_path.read_text(encoding="utf-8").strip()
        if not raw:
            return fallback
        candidate = Path(raw).expanduser()
        if candidate.is_dir():
            return candidate.resolve()
    except Exception:
        # Any read/parse/access issue should fall back to home directory.
        pass
    return fallback


def _extract_plantuml_error_details(stderr_text: str) -> str:
    """Parse PlantUML stderr into a readable, more detailed message."""
    raw = (stderr_text or "").replace("\r\n", "\n").replace("\r", "\n")
    lines = [line.strip() for line in raw.split("\n") if line.strip()]
    if not lines:
        return "unknown error"

    # Common PlantUML stderr shape:
    # ERROR
    # <line-number>
    # <message>
    if len(lines) >= 3 and lines[0].upper() == "ERROR" and lines[1].isdigit():
        return f"line {lines[1]}: {lines[2]}"

    # Fallback: keep the first few lines for context.
    return "\n".join(lines[:8])


def _stamp_pdf_page_numbers(pdf_bytes: bytes, layout_hints: dict[str, object] | None = None) -> bytes:
    """Overlay centered `N of M` footers on every page of a PDF payload."""
    if not pdf_bytes:
        raise ValueError("Empty PDF payload")

    try:
        from pypdf import PageObject, PdfReader, PdfWriter, Transformation
    except Exception as exc:
        raise RuntimeError("Missing dependency 'pypdf' for PDF page numbering") from exc

    try:
        from reportlab.pdfgen import canvas
    except Exception as exc:
        raise RuntimeError("Missing dependency 'reportlab' for PDF page numbering") from exc

    reader = PdfReader(BytesIO(pdf_bytes))
    layout_hints = layout_hints if isinstance(layout_hints, dict) else {}

    def normalize_text(value: str) -> str:
        return re.sub(r"\s+", " ", str(value or "")).strip().casefold()

    landscape_headings = {
        normalize_text(item)
        for item in (layout_hints.get("landscapeHeadings") or [])
        if str(item or "").strip()
    }
    diagram_headings = {
        normalize_text(item)
        for item in (layout_hints.get("diagramHeadings") or [])
        if str(item or "").strip()
    }

    def page_text(page) -> str:
        try:
            return page.extract_text() or ""
        except Exception:
            return ""

    raw_page_texts = [page_text(page) for page in reader.pages]
    normalized_page_texts = [normalize_text(text) for text in raw_page_texts]
    landscape_token = normalize_text("__MDEXPLORE_LANDSCAPE_PAGE__")
    landscape_flags = [
        (landscape_token in page_text) or any(heading and heading in page_text for heading in landscape_headings)
        for page_text in normalized_page_texts
    ]
    diagram_page_flags = [
        any(heading and heading in page_text for heading in diagram_headings)
        for page_text in normalized_page_texts
    ]

    def raster_page_bounds() -> list[tuple[float, float, float, float] | None]:
        if not reader.pages:
            return []
        try:
            import shutil
            import subprocess
            import tempfile
            from pathlib import Path
            from PIL import Image
        except Exception:
            return [None] * len(reader.pages)

        if shutil.which("pdftoppm") is None:
            return [None] * len(reader.pages)

        try:
            with tempfile.TemporaryDirectory(prefix="mdexplore-pdf-bounds-") as tmpdir_str:
                tmpdir = Path(tmpdir_str)
                pdf_path = tmpdir / "input.pdf"
                prefix = tmpdir / "page"
                pdf_path.write_bytes(pdf_bytes)
                result = subprocess.run(
                    ["pdftoppm", "-png", "-r", "72", str(pdf_path), str(prefix)],
                    capture_output=True,
                    check=False,
                    timeout=60,
                )
                if result.returncode != 0:
                    return [None] * len(reader.pages)

                bounds_by_index: list[tuple[float, float, float, float] | None] = [None] * len(reader.pages)
                image_paths = sorted(tmpdir.glob("page-*.png"))
                for image_path in image_paths:
                    match = re.search(r"-(\d+)\.png$", image_path.name)
                    if not match:
                        continue
                    page_index = int(match.group(1)) - 1
                    if page_index < 0 or page_index >= len(reader.pages):
                        continue
                    image = Image.open(image_path).convert("RGB")
                    width_px, height_px = image.size
                    if width_px <= 0 or height_px <= 0:
                        continue
                    pixels = image.load()
                    minx, miny = width_px, height_px
                    maxx = maxy = -1
                    for y in range(height_px):
                        for x in range(width_px):
                            r, g, b = pixels[x, y]
                            if r < 247 or g < 247 or b < 247:
                                if x < minx:
                                    minx = x
                                if y < miny:
                                    miny = y
                                if x > maxx:
                                    maxx = x
                                if y > maxy:
                                    maxy = y
                    if maxx < 0 or maxy < 0:
                        continue
                    pad_x = max(4, int((maxx - minx + 1) * 0.025))
                    pad_y = max(4, int((maxy - miny + 1) * 0.025))
                    minx = max(0, minx - pad_x)
                    miny = max(0, miny - pad_y)
                    maxx = min(width_px - 1, maxx + pad_x)
                    maxy = min(height_px - 1, maxy + pad_y)
                    page = reader.pages[page_index]
                    page_width = float(page.mediabox.width)
                    page_height = float(page.mediabox.height)
                    crop_left = (minx / width_px) * page_width
                    crop_right = ((maxx + 1) / width_px) * page_width
                    crop_top = (miny / height_px) * page_height
                    crop_bottom = ((maxy + 1) / height_px) * page_height
                    lower_y = max(0.0, page_height - crop_bottom)
                    upper_y = min(page_height, page_height - crop_top)
                    bounds_by_index[page_index] = (crop_left, lower_y, crop_right, upper_y)
                return bounds_by_index
        except Exception:
            return [None] * len(reader.pages)

    crop_bounds_by_page = raster_page_bounds()

    def page_has_meaningful_content(page, extracted_text: str) -> bool:
        """Suppress fully blank pages before footer numbering is applied."""
        text = extracted_text.strip()
        if text:
            return True

        try:
            annotations = page.get("/Annots")
        except Exception:
            annotations = None
        if annotations:
            return True

        try:
            resources = page.get("/Resources")
        except Exception:
            resources = None
        if resources:
            try:
                xobjects = resources.get("/XObject")
            except Exception:
                xobjects = None
            if xobjects:
                try:
                    if len(xobjects) > 0:
                        return True
                except Exception:
                    return True

        try:
            contents = page.get_contents()
        except Exception:
            contents = None
        if contents is None:
            return False

        streams = contents if isinstance(contents, list) else [contents]
        paint_tokens = (
            " Do",
            " S",
            " s",
            " f",
            " f*",
            " F",
            " B",
            " B*",
            " b",
            " b*",
            " sh",
            " Tj",
            " TJ",
            " '",
            ' "',
        )
        for stream in streams:
            try:
                raw = stream.get_data()
            except Exception:
                continue
            if not raw:
                continue
            text_stream = raw.decode("latin-1", errors="ignore")
            if any(token in text_stream for token in paint_tokens):
                return True

        return False

    kept_page_records = [
        (page, landscape, is_diagram_page, crop_bounds)
        for page, landscape, is_diagram_page, crop_bounds, extracted_text in zip(
            reader.pages,
            landscape_flags,
            diagram_page_flags,
            crop_bounds_by_page,
            raw_page_texts,
        )
        if page_has_meaningful_content(page, extracted_text)
    ]
    if not kept_page_records:
        kept_page_records = [
            (page, landscape, is_diagram_page, crop_bounds)
            for page, landscape, is_diagram_page, crop_bounds in zip(
                reader.pages,
                landscape_flags,
                diagram_page_flags,
                crop_bounds_by_page,
            )
        ]

    page_total = len(kept_page_records)
    if page_total <= 0:
        raise RuntimeError("Generated PDF has no pages")

    def estimate_majority_font_size() -> float:
        """Infer dominant body font size from PDF text operators."""
        size_counts: dict[float, int] = {}
        for page, _is_landscape, _is_diagram_page, _crop_bounds in kept_page_records[: min(5, page_total)]:
            try:
                contents = page.get_contents()
            except Exception:
                contents = None
            if contents is None:
                continue

            streams = contents if isinstance(contents, list) else [contents]
            for stream in streams:
                try:
                    raw = stream.get_data()
                except Exception:
                    continue
                if not raw:
                    continue
                text = raw.decode("latin-1", errors="ignore")
                for match in re.finditer(r"([0-9]+(?:\\.[0-9]+)?)\\s+Tf\\b", text):
                    try:
                        size = float(match.group(1))
                    except Exception:
                        continue
                    if 6.0 <= size <= 24.0:
                        bucket = round(size * 2.0) / 2.0
                        size_counts[bucket] = size_counts.get(bucket, 0) + 1

        if not size_counts:
            return 10.5
        return max(size_counts.items(), key=lambda item: (item[1], -abs(item[0] - 11.0)))[0]

    def estimate_page_diagram_font_size(page) -> float:
        """Approximate the largest non-heading font size used on a page."""
        try:
            contents = page.get_contents()
        except Exception:
            contents = None
        if contents is None:
            return 0.0

        candidate_sizes: list[float] = []
        streams = contents if isinstance(contents, list) else [contents]
        for stream in streams:
            try:
                raw = stream.get_data()
            except Exception:
                continue
            if not raw:
                continue
            text = raw.decode("latin-1", errors="ignore")
            for match in re.finditer(r"([0-9]+(?:\\.[0-9]+)?)\\s+Tf\\b", text):
                try:
                    size = float(match.group(1))
                except Exception:
                    continue
                if 6.0 <= size <= 20.0:
                    candidate_sizes.append(size)
        if not candidate_sizes:
            return 0.0
        return max(candidate_sizes)

    base_body_font_size = estimate_majority_font_size()

    writer = PdfWriter()
    for page_number, (page, is_landscape_page, is_diagram_page, crop_bounds) in enumerate(kept_page_records, start=1):
        source_width = float(page.mediabox.width)
        source_height = float(page.mediabox.height)
        if source_width <= 0 or source_height <= 0:
            writer.add_page(page)
            continue

        crop_left = crop_bottom = 0.0
        crop_right = source_width
        crop_top = source_height
        if crop_bounds is not None and (is_diagram_page or is_landscape_page):
            crop_left, crop_bottom, crop_right, crop_top = crop_bounds
            crop_left = max(0.0, min(source_width - 1.0, crop_left))
            crop_right = max(crop_left + 1.0, min(source_width, crop_right))
            crop_bottom = max(0.0, min(source_height - 1.0, crop_bottom))
            crop_top = max(crop_bottom + 1.0, min(source_height, crop_top))

        content_source_width = crop_right - crop_left
        content_source_height = crop_top - crop_bottom

        page_width = source_height if is_landscape_page else source_width
        page_height = source_width if is_landscape_page else source_height

        # Fit rendered content into a print-style content box with explicit
        # top/side margins plus a dedicated footer band for page numbers.
        side_margin = max(34.0, min(page_width * 0.12, base_body_font_size * 4.2))
        top_margin = max(30.0, min(page_height * 0.10, base_body_font_size * 3.8))
        footer_band_height = max(42.0, min(page_height * 0.16, base_body_font_size * 4.4))
        content_box_width = max(72.0, page_width - (2.0 * side_margin))
        content_box_height = max(72.0, page_height - top_margin - footer_band_height)

        max_safe_scale = 1.0
        if is_diagram_page or is_landscape_page:
            page_diagram_font_size = estimate_page_diagram_font_size(page)
            if page_diagram_font_size > 0:
                max_safe_scale = max(1.0, min(2.75, 16.0 / page_diagram_font_size))
            else:
                max_safe_scale = 2.75 if is_landscape_page else 1.8
        content_scale = min(
            max_safe_scale,
            content_box_width / content_source_width,
            content_box_height / content_source_height,
        )
        content_width = content_source_width * content_scale
        content_height = content_source_height * content_scale
        content_translate_x = side_margin + max(0.0, (content_box_width - content_width) / 2.0)
        content_translate_y = footer_band_height + max(0.0, (content_box_height - content_height) / 2.0)

        composed_page = PageObject.create_blank_page(width=page_width, height=page_height)
        if is_landscape_page:
            transform = (
                Transformation()
                .scale(content_scale, content_scale)
                .translate(content_translate_x - (crop_left * content_scale), content_translate_y - (crop_bottom * content_scale))
            )
        else:
            transform = Transformation().scale(content_scale, content_scale).translate(
                content_translate_x - (crop_left * content_scale),
                content_translate_y - (crop_bottom * content_scale),
            )
        composed_page.merge_transformed_page(page, transform, over=True)

        footer_font_size = max(8.0, min(14.0, base_body_font_size * content_scale))
        footer_baseline_y = max(12.0, (footer_band_height - footer_font_size) / 2.0)

        overlay_buffer = BytesIO()
        footer_canvas = canvas.Canvas(overlay_buffer, pagesize=(page_width, page_height))
        footer_canvas.setFont("Helvetica", footer_font_size)
        footer_text = f"{page_number} of {page_total}"
        footer_width = footer_canvas.stringWidth(footer_text, "Helvetica", footer_font_size)
        x = max(0.0, (page_width - footer_width) / 2.0)
        footer_canvas.drawString(x, footer_baseline_y, footer_text)
        footer_canvas.save()

        overlay_buffer.seek(0)
        overlay_pdf = PdfReader(overlay_buffer)
        if overlay_pdf.pages:
            composed_page.merge_page(overlay_pdf.pages[0])
        writer.add_page(composed_page)

    output = BytesIO()
    writer.write(output)
    return output.getvalue()


def _build_markdown_icon() -> QIcon:
    """Return a standard markdown icon (theme icon with a drawn fallback)."""

    def color_distance(a: QColor, b: QColor) -> int:
        return abs(a.red() - b.red()) + abs(a.green() - b.green()) + abs(a.blue() - b.blue())

    def transparentize_outer_background(pixmap: QPixmap) -> QPixmap:
        # Convert border-connected background pixels to transparent while
        # preserving the interior icon artwork.
        image = pixmap.toImage().convertToFormat(QImage.Format.Format_ARGB32)
        w = image.width()
        h = image.height()
        if w <= 0 or h <= 0:
            return pixmap

        corners = [
            image.pixelColor(0, 0),
            image.pixelColor(w - 1, 0),
            image.pixelColor(0, h - 1),
            image.pixelColor(w - 1, h - 1),
        ]

        # If corners are already transparent, keep the source image unchanged.
        if all(c.alpha() == 0 for c in corners):
            return pixmap

        threshold = 36

        def is_background(c: QColor) -> bool:
            for bg in corners:
                if color_distance(c, bg) <= threshold:
                    return True
            return False

        visited = bytearray(w * h)
        queue: deque[tuple[int, int]] = deque()

        def push(x: int, y: int) -> None:
            idx = y * w + x
            if visited[idx]:
                return
            color = image.pixelColor(x, y)
            if not is_background(color):
                return
            visited[idx] = 1
            queue.append((x, y))

        for x in range(w):
            push(x, 0)
            push(x, h - 1)
        for y in range(h):
            push(0, y)
            push(w - 1, y)

        while queue:
            x, y = queue.popleft()
            c = image.pixelColor(x, y)
            c.setAlpha(0)
            image.setPixelColor(x, y, c)

            if x > 0:
                push(x - 1, y)
            if x + 1 < w:
                push(x + 1, y)
            if y > 0:
                push(x, y - 1)
            if y + 1 < h:
                push(x, y + 1)

        return QPixmap.fromImage(image)

    def fit_icon_canvas(pixmap: QPixmap) -> QPixmap:
        # Trim excess transparent padding and place the art on a square icon
        # canvas so desktop launchers render it at a readable size.
        image = pixmap.toImage().convertToFormat(QImage.Format.Format_ARGB32)
        w = image.width()
        h = image.height()
        if w <= 0 or h <= 0:
            return pixmap

        minx, miny = w, h
        maxx, maxy = -1, -1
        for y in range(h):
            for x in range(w):
                if image.pixelColor(x, y).alpha() > 20:
                    if x < minx:
                        minx = x
                    if y < miny:
                        miny = y
                    if x > maxx:
                        maxx = x
                    if y > maxy:
                        maxy = y

        if maxx < minx or maxy < miny:
            return pixmap

        cropped = QPixmap.fromImage(image.copy(minx, miny, maxx - minx + 1, maxy - miny + 1))

        size = 256
        # Keep only a tiny safety inset so icon art occupies as much of the
        # launcher tile as possible while still preserving aspect ratio.
        inset = 2
        max_w = size - (2 * inset)
        max_h = size - (2 * inset)
        scaled = cropped.scaled(max_w, max_h, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation)

        canvas = QPixmap(size, size)
        canvas.fill(Qt.GlobalColor.transparent)
        painter = QPainter(canvas)
        painter.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        x = (size - scaled.width()) // 2
        y = (size - scaled.height()) // 2
        painter.drawPixmap(x, y, scaled)
        painter.end()
        return canvas

    for icon_name in ("mdexplor-icon.png", "mdexplor-icon.webp", "mdexplore-icon.webp"):
        icon_path = Path(__file__).resolve().with_name(icon_name)
        if icon_path.exists():
            asset_pixmap = QPixmap(str(icon_path))
            if not asset_pixmap.isNull():
                cleaned = transparentize_outer_background(asset_pixmap)
                print(f"mdexplore icon source: {icon_path}", file=sys.stderr)
                return QIcon(fit_icon_canvas(cleaned))

    pixmap = QPixmap(64, 64)
    pixmap.fill(Qt.GlobalColor.transparent)

    painter = QPainter(pixmap)
    painter.setRenderHint(QPainter.RenderHint.Antialiasing)
    painter.setPen(Qt.PenStyle.NoPen)
    painter.setBrush(QColor("#2f81f7"))
    painter.drawRoundedRect(4, 8, 56, 48, 8, 8)

    pen = QPen(QColor("#ffffff"))
    pen.setWidth(4)
    pen.setCapStyle(Qt.PenCapStyle.RoundCap)
    pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
    painter.setPen(pen)
    painter.setBrush(Qt.BrushStyle.NoBrush)

    # Stylized "M"
    painter.drawLine(14, 42, 14, 22)
    painter.drawLine(14, 22, 22, 34)
    painter.drawLine(22, 34, 30, 22)
    painter.drawLine(30, 22, 30, 42)

    # Down arrow
    painter.drawLine(42, 22, 42, 38)
    painter.drawLine(37, 33, 42, 38)
    painter.drawLine(47, 33, 42, 38)
    painter.end()

    print("mdexplore icon source: built-in fallback", file=sys.stderr)
    return QIcon(pixmap)


def _build_clear_x_icon() -> QIcon:
    """Return a small, explicit X icon for the search-field clear action."""
    pixmap = QPixmap(14, 14)
    pixmap.fill(Qt.GlobalColor.transparent)
    painter = QPainter(pixmap)
    painter.setRenderHint(QPainter.RenderHint.Antialiasing)
    pen = QPen(QColor("#9ca3af"))
    pen.setWidth(2)
    pen.setCapStyle(Qt.PenCapStyle.RoundCap)
    painter.setPen(pen)
    painter.drawLine(3, 3, 11, 11)
    painter.drawLine(11, 3, 3, 11)
    painter.end()
    return QIcon(pixmap)


def _load_svg_icon(filename: str, color: QColor, size: int = 16) -> QIcon:
    """Load and recolor a local SVG icon to a fixed flat color."""
    icon_path = Path(__file__).resolve().parent / filename
    if icon_path.is_file():
        renderer = QSvgRenderer(str(icon_path))
        if not renderer.isValid():
            return QIcon()
        pixmap = QPixmap(size, size)
        pixmap.fill(Qt.GlobalColor.transparent)
        painter = QPainter(pixmap)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        painter.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform, True)
        renderer.render(painter)
        painter.end()

        image = pixmap.toImage().convertToFormat(QImage.Format.Format_ARGB32)
        target = QColor(color)
        for y in range(image.height()):
            for x in range(image.width()):
                pixel = image.pixelColor(x, y)
                alpha = pixel.alpha()
                if alpha < 16:
                    image.setPixelColor(x, y, QColor(0, 0, 0, 0))
                    continue
                image.setPixelColor(x, y, QColor(target.red(), target.green(), target.blue(), alpha))
        return QIcon(QPixmap.fromImage(image))
    return QIcon()


class ColorizedMarkdownModel(QFileSystemModel):
    """Filesystem model with per-directory persisted file highlight colors."""

    COLOR_FILE_NAME = ".mdexplore-colors.json"
    _ICON_SIZE = 16
    _ICON_GAP = 2
    _VIEWS_ICON_SIZE = 13
    _SEARCH_ICON_SIZE = 8
    _SEARCH_SLOT_WIDTH = 10
    _GUTTER_WIDTH = _SEARCH_SLOT_WIDTH + (_ICON_SIZE + _ICON_GAP)

    def __init__(self, parent=None) -> None:
        super().__init__(parent)
        # Cache both persistence data and the small finite set of tree icons so
        # the view stays responsive even in large directories.
        self._dir_color_map: dict[str, dict[str, str]] = {}
        self._loaded_dirs: set[str] = set()
        self._search_match_paths: set[str] = set()
        self._multi_view_paths: set[str] = set()
        self._markdown_icon = _load_svg_icon("markdown.svg", QColor("#bcc5d1"))
        if self._markdown_icon.isNull():
            self._markdown_icon = _build_markdown_icon()
        self._views_icon = _load_svg_icon("views.svg", QColor("#bcc5d1"))
        self._search_hit_icon = _load_svg_icon("search-hit.svg", QColor("#f5d34f"))
        self._decorated_icon_cache: dict[tuple[bool, bool], QIcon] = {}

    def data(self, index, role=Qt.ItemDataRole.DisplayRole):
        # This model only customizes markdown files; directories continue to use
        # QFileSystemModel defaults so tree navigation behavior remains native.
        if role == Qt.ItemDataRole.DecorationRole:
            info = self.fileInfo(index)
            if info.isFile() and info.suffix().lower() == "md":
                path_key = self._path_key(Path(info.filePath()))
                has_search_match = path_key in self._search_match_paths
                has_multi_view = path_key in self._multi_view_paths
                return self._decorated_markdown_icon(has_multi_view, has_search_match)
        if role == Qt.ItemDataRole.ForegroundRole:
            info = self.fileInfo(index)
            if info.isFile() and info.suffix().lower() == "md":
                color_name = self._color_for_file(Path(info.filePath()))
                if color_name:
                    color = QColor(color_name)
                    if color.isValid():
                        luminance = (0.299 * color.redF()) + (0.587 * color.greenF()) + (0.114 * color.blueF())
                        return QBrush(QColor("#101418") if luminance > 0.6 else QColor("#f8fafc"))
        if role == Qt.ItemDataRole.FontRole:
            info = self.fileInfo(index)
            if info.isFile() and info.suffix().lower() == "md":
                if self._path_key(Path(info.filePath())) in self._search_match_paths:
                    base_font = super().data(index, role)
                    font = QFont(base_font) if isinstance(base_font, QFont) else QFont()
                    font.setBold(True)
                    font.setItalic(True)
                    return font
        return super().data(index, role)

    def set_color_for_file(self, path: Path, color_name: str | None) -> None:
        # Persist selected color immediately and notify the view.
        directory = path.parent
        color_map = self._load_directory_colors(directory)
        if color_name:
            color_map[path.name] = color_name
        else:
            color_map.pop(path.name, None)
        self._save_directory_colors(directory)

        index = self.index(str(path))
        if index.isValid():
            self.dataChanged.emit(
                index,
                index,
                [Qt.ItemDataRole.ForegroundRole],
            )

    def highlight_background_for_path(self, path: Path) -> QColor | None:
        color_name = self._color_for_file(path)
        if not color_name:
            return None
        color = QColor(color_name)
        return color if color.isValid() else None

    def highlight_foreground_for_path(self, path: Path) -> QColor | None:
        background = self.highlight_background_for_path(path)
        if background is None:
            return None
        luminance = (
            (0.299 * background.redF())
            + (0.587 * background.greenF())
            + (0.114 * background.blueF())
        )
        return QColor("#101418") if luminance > 0.6 else QColor("#f8fafc")

    def collect_files_with_color(self, root: Path, color_name: str) -> list[Path]:
        """Return files under root that are persisted with the requested color."""
        if not root.is_dir():
            return []
        normalized_color = color_name.lower()
        matches: list[Path] = []

        def on_walk_error(_err) -> None:
            # Permission errors are expected in some trees; skip quietly.
            return

        for dirpath, _dirnames, _filenames in os.walk(root, onerror=on_walk_error, followlinks=False):
            directory = Path(dirpath)
            color_map = self._load_directory_colors(directory)
            for file_name, file_color in color_map.items():
                if file_color.lower() != normalized_color:
                    continue
                candidate = directory / file_name
                try:
                    if candidate.is_file():
                        matches.append(candidate.resolve())
                except Exception:
                    # Broken symlink or inaccessible file; ignore quietly.
                    pass

        matches.sort(key=str)
        return matches

    def clear_all_highlights(self, root: Path) -> int:
        """Clear all persisted highlights under root recursively."""
        if not root.is_dir():
            return 0

        cleared_entries = 0

        def on_walk_error(_err) -> None:
            # Permission errors are expected in some trees; skip quietly.
            return

        for dirpath, _dirnames, _filenames in os.walk(root, onerror=on_walk_error, followlinks=False):
            directory = Path(dirpath)
            color_map = self._load_directory_colors(directory)
            if not color_map:
                continue
            cleared_entries += len(color_map)
            color_map.clear()
            self._save_directory_colors(directory)

        return cleared_entries

    def _color_for_file(self, path: Path) -> str | None:
        color_map = self._load_directory_colors(path.parent)
        return color_map.get(path.name)

    def set_search_match_paths(self, paths: set[Path]) -> None:
        self._search_match_paths = {self._path_key(path) for path in paths}

    def clear_search_match_paths(self) -> None:
        self._search_match_paths.clear()

    def set_multi_view_paths(self, paths: set[Path]) -> None:
        self._multi_view_paths = {self._path_key(path) for path in paths}

    def clear_multi_view_paths(self) -> None:
        self._multi_view_paths.clear()

    def _path_key(self, path: Path) -> str:
        try:
            return str(path.resolve())
        except Exception:
            return str(path)

    def _directory_key(self, directory: Path) -> str:
        return str(directory)

    def _load_directory_colors(self, directory: Path) -> dict[str, str]:
        # Load once per directory and cache the mapping in-memory.
        key = self._directory_key(directory)
        if key in self._loaded_dirs:
            return self._dir_color_map.setdefault(key, {})

        self._loaded_dirs.add(key)
        color_map: dict[str, str] = {}
        color_file = directory / self.COLOR_FILE_NAME
        try:
            raw = color_file.read_text(encoding="utf-8")
            payload = json.loads(raw)
            if isinstance(payload, dict):
                files_payload = payload.get("files", payload)
                if isinstance(files_payload, dict):
                    for name, color in files_payload.items():
                        if isinstance(name, str) and isinstance(color, str):
                            color_map[name] = color
        except Exception:
            # Missing file, access denied, or malformed JSON should not block browsing.
            pass

        self._dir_color_map[key] = color_map
        return color_map

    def _save_directory_colors(self, directory: Path) -> None:
        # Writes are intentionally best-effort; unwritable directories are
        # expected in some user environments.
        key = self._directory_key(directory)
        color_map = self._dir_color_map.get(key, {})
        color_file = directory / self.COLOR_FILE_NAME
        try:
            if color_map:
                payload = {"files": dict(sorted(color_map.items()))}
                color_file.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
            elif color_file.exists():
                color_file.unlink()
        except Exception:
            # Requested behavior: fail quietly when persistence can't be written.
            pass

    @classmethod
    def decorated_icon_size(cls) -> QSize:
        return QSize(cls._GUTTER_WIDTH + cls._ICON_SIZE, cls._ICON_SIZE)

    def _decorated_markdown_icon(self, has_multi_view: bool, has_search_match: bool) -> QIcon:
        cache_key = (has_multi_view, has_search_match)
        cached = self._decorated_icon_cache.get(cache_key)
        if cached is not None:
            return cached

        total_width = self._ICON_SIZE + self._GUTTER_WIDTH
        total_height = self._ICON_SIZE
        canvas = QPixmap(total_width, total_height)
        canvas.fill(Qt.GlobalColor.transparent)
        painter = QPainter(canvas)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        painter.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform, True)

        if has_search_match:
            search_pixmap = self._search_hit_icon.pixmap(
                self._SEARCH_ICON_SIZE, self._SEARCH_ICON_SIZE
            )
            search_x = max(0, (self._SEARCH_SLOT_WIDTH - self._SEARCH_ICON_SIZE) // 2)
            search_y = max(0, (self._ICON_SIZE - self._SEARCH_ICON_SIZE) // 2)
            painter.drawPixmap(search_x, search_y, search_pixmap)
        if has_multi_view:
            views_pixmap = self._views_icon.pixmap(self._VIEWS_ICON_SIZE, self._VIEWS_ICON_SIZE)
            views_x = self._SEARCH_SLOT_WIDTH + self._ICON_GAP
            views_y = max(0, (self._ICON_SIZE - self._VIEWS_ICON_SIZE) // 2)
            painter.drawPixmap(views_x, views_y, views_pixmap)

        icon_pixmap = self._markdown_icon.pixmap(self._ICON_SIZE, self._ICON_SIZE)
        painter.drawPixmap(self._GUTTER_WIDTH, 0, icon_pixmap)
        painter.end()

        decorated = QIcon(canvas)
        self._decorated_icon_cache[cache_key] = decorated
        return decorated


class MarkdownTreeItemDelegate(QStyledItemDelegate):
    """Paint filename-only highlight backgrounds for markdown rows."""

    def paint(self, painter: QPainter, option, index) -> None:
        model = index.model()
        if not isinstance(model, ColorizedMarkdownModel):
            super().paint(painter, option, index)
            return

        info = model.fileInfo(index)
        if not (info.isFile() and info.suffix().lower() == "md"):
            super().paint(painter, option, index)
            return

        file_path = Path(info.filePath())
        background = model.highlight_background_for_path(file_path)
        if background is None:
            super().paint(painter, option, index)
            return

        super().paint(painter, option, index)

        opt = QStyleOptionViewItem(option)
        self.initStyleOption(opt, index)
        widget = opt.widget
        style = widget.style() if widget is not None else QApplication.style()

        text_rect = style.subElementRect(QStyle.SubElement.SE_ItemViewItemText, opt, widget)
        highlight_rect = text_rect.adjusted(-2, 1, 2, -1)
        painter.save()
        painter.setPen(Qt.PenStyle.NoPen)
        painter.setBrush(background)
        painter.drawRect(highlight_rect)
        painter.restore()

        foreground = model.highlight_foreground_for_path(file_path)
        text_color = foreground if foreground is not None else opt.palette.color(QPalette.ColorRole.Text)
        painter.save()
        painter.setFont(opt.font)
        painter.setPen(text_color)
        elided_text = opt.fontMetrics.elidedText(opt.text, opt.textElideMode, text_rect.width())
        alignment = int(opt.displayAlignment | Qt.AlignmentFlag.AlignVCenter)
        painter.drawText(text_rect, alignment, elided_text)
        painter.restore()


class MarkdownRenderer:
    """Converts markdown to HTML with Mermaid, MathJax, and PlantUML support."""

    def __init__(self, mermaid_backend: str = MERMAID_BACKEND_JS) -> None:
        # Backend selection is resolved once per renderer so the markdown fence
        # callbacks can stay simple and deterministic.
        self._mermaid_backend_requested = str(mermaid_backend or MERMAID_BACKEND_JS).strip().lower()
        if self._mermaid_backend_requested not in {MERMAID_BACKEND_JS, MERMAID_BACKEND_RUST}:
            self._mermaid_backend_requested = MERMAID_BACKEND_JS
        self._mermaid_rs_binary = self._resolve_mermaid_rs_binary()
        self._mermaid_rs_setup_issue = self._mermaid_rs_setup_error()
        if self._mermaid_backend_requested == MERMAID_BACKEND_RUST and self._mermaid_rs_setup_issue is None:
            self._mermaid_backend = MERMAID_BACKEND_RUST
        else:
            self._mermaid_backend = MERMAID_BACKEND_JS
        self._mermaid_svg_cache: dict[str, str] = {}
        self._last_mermaid_pdf_svg_by_hash: dict[str, str] = {}
        self._mathjax_local_script = self._resolve_local_mathjax_script()
        self._mermaid_local_script = self._resolve_local_mermaid_script()
        self._plantuml_jar_path = self._resolve_plantuml_jar_path()
        self._plantuml_setup_issue = self._plantuml_setup_error()
        self._plantuml_svg_cache: dict[str, str] = {}
        self._md = MarkdownIt(
            "commonmark",
            {"html": True, "linkify": True, "typographer": True},
        ).enable("table").enable("strikethrough")
        # Parse $...$ / $$...$$ as dedicated math tokens before markdown
        # emphasis/underscore rules run, preventing TeX corruption.
        self._md.use(dollarmath_plugin)

        default_fence = self._md.renderer.rules["fence"]
        default_render_token = self._md.renderer.renderToken

        def custom_math_inline(tokens, idx, options, env):
            token = tokens[idx]
            # Keep TeX content raw for MathJax, only HTML-escape unsafe chars.
            return f"${html.escape(token.content)}$"

        def custom_math_block(tokens, idx, options, env):
            token = tokens[idx]
            line_attrs = ""
            if token.map and len(token.map) == 2:
                line_attrs = f' data-md-line-start="{token.map[0]}" data-md-line-end="{token.map[1]}"'
            math_body = (token.content or "").strip("\n")
            return f'<div class="mdexplore-math-block"{line_attrs}>$$\n{html.escape(math_body)}\n$$</div>\n'

        def custom_fence(tokens, idx, options, env):
            # Intercept known diagram fences and delegate the rest to the
            # default fenced-code renderer. This is the only place where raw
            # markdown fence language is turned into preview/PDF placeholders.
            token = tokens[idx]
            info = token.info.strip().split(maxsplit=1)[0].lower() if token.info else ""
            code = token.content
            line_attrs = ""
            if token.map and len(token.map) == 2:
                line_attrs = f' data-md-line-start="{token.map[0]}" data-md-line-end="{token.map[1]}"'

            if info == "mermaid":
                try:
                    # All Mermaid flows start by normalizing source and hashing
                    # it. The hash is the cache key shared by preview, restore,
                    # and PDF-specific SVG variants.
                    prepared_source = self._prepare_mermaid_source(code)
                    mermaid_hash = hashlib.sha1(prepared_source.encode("utf-8", errors="replace")).hexdigest()
                    mermaid_index = int(env.get("mermaid_index", 0)) if isinstance(env, dict) else 0
                    if isinstance(env, dict):
                        env["mermaid_index"] = mermaid_index + 1
                    if self._mermaid_backend == MERMAID_BACKEND_RUST:
                        # Rust preview and PDF SVGs intentionally fork here:
                        # preview gets mdexplore's GUI profile, while PDF gets
                        # a separate vanilla render cached for export only.
                        svg_markup, error_message = self._render_mermaid_svg_markup(prepared_source, "preview")
                        if isinstance(env, dict):
                            pdf_svg_map = env.get("mermaid_pdf_svg_by_hash")
                            if isinstance(pdf_svg_map, dict) and mermaid_hash not in pdf_svg_map:
                                pdf_svg, _pdf_error = self._render_mermaid_svg_markup(prepared_source, "pdf")
                                if pdf_svg:
                                    pdf_svg_map[mermaid_hash] = pdf_svg
                        source_attr = html.escape(prepared_source, quote=True)
                        if svg_markup is not None:
                            return (
                                f'<div class="mdexplore-fence"{line_attrs}>'
                                f'<div class="mermaid mermaid-ready" data-mdexplore-mermaid-backend="rust" '
                                f'data-mdexplore-mermaid-hash="{mermaid_hash}" '
                                f'data-mdexplore-mermaid-index="{mermaid_index}" '
                                f'data-mdexplore-mermaid-source="{source_attr}">\n{svg_markup}\n</div>'
                                "</div>\n"
                            )
                        safe_error_attr = html.escape(error_message or "Rust Mermaid rendering failed", quote=True)
                        return (
                            f'<div class="mdexplore-fence"{line_attrs}>'
                            f'<div class="mermaid mermaid-rust-fallback" data-mdexplore-mermaid-backend="rust" '
                            f'data-mdexplore-mermaid-hash="{mermaid_hash}" '
                            f'data-mdexplore-mermaid-index="{mermaid_index}" '
                            f'data-mdexplore-mermaid-source="{source_attr}" '
                            f'data-mdexplore-rust-error="{safe_error_attr}">'
                            "Mermaid rendering..."
                            "</div>"
                            "</div>\n"
                        )
                    return (
                        f'<div class="mdexplore-fence"{line_attrs}>'
                        f'<div class="mermaid" data-mdexplore-mermaid-hash="{mermaid_hash}" '
                        f'data-mdexplore-mermaid-index="{mermaid_index}">\n{html.escape(code)}\n</div>'
                        "</div>\n"
                    )
                except Exception as exc:
                    safe_error = html.escape(str(exc) or "unexpected Mermaid rendering error")
                    return (
                        f'<div class="mdexplore-fence mermaid-error"{line_attrs}>'
                        f'<div class="mermaid mermaid-error">Mermaid render failed: {safe_error}</div>'
                        "</div>\n"
                    )

            if info in {"plantuml", "puml", "uml"}:
                # PlantUML takes a different path because preview rendering is
                # progressive and may complete after the rest of the markdown is
                # already visible.
                resolver = env.get("plantuml_resolver") if isinstance(env, dict) else None
                if callable(resolver):
                    plantuml_index = int(env.get("plantuml_index", 0))
                    env["plantuml_index"] = plantuml_index + 1
                    return resolver(code, plantuml_index, line_attrs)

                data_uri, error_message = self._render_plantuml_data_uri(code)
                if data_uri is not None:
                    return (
                        f'<div class="mdexplore-fence"{line_attrs}>'
                        f'<img class="plantuml" src="{data_uri}" alt="PlantUML diagram"/>'
                        "</div>\n"
                    )

                escaped_error = html.escape(error_message or "PlantUML rendering failed")
                escaped_code = html.escape(code)
                return (
                    f'<div class="mdexplore-fence plantuml-error"{line_attrs}>'
                    f'<div class="plantuml-error-message">{escaped_error}</div>'
                    f'<pre><code class="language-plantuml">{escaped_code}</code></pre>'
                    "</div>\n"
                )

            return default_fence(tokens, idx, options, env)

        def custom_render_token(tokens, idx, options, env):
            # Attach source-line metadata so preview selections can map back
            # to source markdown ranges for copy operations.
            token = tokens[idx]
            if token.nesting == 1 and token.type.endswith("_open") and token.map and len(token.map) == 2:
                token.attrSet("data-md-line-start", str(token.map[0]))
                token.attrSet("data-md-line-end", str(token.map[1]))
            return default_render_token(tokens, idx, options, env)

        self._md.renderer.rules["fence"] = custom_fence
        self._md.renderer.rules["math_inline"] = custom_math_inline
        self._md.renderer.rules["math_block"] = custom_math_block
        self._md.renderer.renderToken = custom_render_token

    @property
    def mermaid_backend(self) -> str:
        """Return active Mermaid backend (`js` or `rust`)."""
        return self._mermaid_backend

    @property
    def mermaid_backend_requested(self) -> str:
        """Return requested Mermaid backend from CLI/config."""
        return self._mermaid_backend_requested

    def mermaid_backend_warning(self) -> str | None:
        """Describe why requested Mermaid backend could not be activated."""
        if self._mermaid_backend_requested == MERMAID_BACKEND_RUST and self._mermaid_backend != MERMAID_BACKEND_RUST:
            return self._mermaid_rs_setup_issue or "Rust Mermaid backend unavailable"
        return None

    def _resolve_mermaid_rs_binary(self) -> Path | None:
        """Locate mmdr executable for Rust Mermaid rendering."""
        env_value = os.environ.get("MDEXPLORE_MERMAID_RS_BIN", "").strip()
        candidates: list[Path] = []
        if env_value:
            candidates.append(Path(env_value).expanduser())

        app_dir = Path(__file__).resolve().parent
        candidates.extend(
            [
                Path.home() / ".cargo" / "bin" / "mmdr",
                app_dir / "vendor" / "mermaid-rs-renderer" / "target" / "release" / "mmdr",
                app_dir / "vendor" / "mermaid-rs-renderer" / "mmdr",
                app_dir / "vendor" / "mermaid-rs-renderer" / "bin" / "mmdr",
                app_dir / "mermaid-rs-renderer" / "target" / "release" / "mmdr",
                app_dir / "mmdr",
            ]
        )

        for candidate in candidates:
            try:
                if candidate.is_file() and os.access(candidate, os.X_OK):
                    return candidate.resolve()
            except Exception:
                continue

        for name in ("mmdr", "mermaid-rs-renderer"):
            found = shutil.which(name)
            if found:
                try:
                    return Path(found).resolve()
                except Exception:
                    return Path(found)
        return None

    def _mermaid_rs_setup_error(self) -> str | None:
        """Return setup issue text when Rust Mermaid backend is unavailable."""
        if self._mermaid_rs_binary is None:
            return (
                "mmdr executable not found "
                "(set MDEXPLORE_MERMAID_RS_BIN or install mermaid-rs-renderer)"
            )
        return None

    def _render_mermaid_svg_markup(self, code: str, render_profile: str = "preview") -> tuple[str | None, str | None]:
        """Render Mermaid source through Rust mmdr backend and return raw SVG."""
        if self._mermaid_rs_setup_issue is not None:
            return None, self._mermaid_rs_setup_issue
        if self._mermaid_rs_binary is None:
            return None, "mmdr executable not available"

        profile = str(render_profile or "preview").strip().lower()
        if profile not in {"preview", "pdf"}:
            profile = "preview"
        prepared_source = self._prepare_mermaid_source(code)
        if profile == "preview":
            rust_theme_config = self._rust_mermaid_theme_config()
            config_signature = json.dumps(rust_theme_config, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        else:
            # PDF-mode Rust rendering should stay vanilla/default.
            rust_theme_config = None
            config_signature = "__MDEXPLORE_RUST_DEFAULT_THEME__"
        cache_key = hashlib.sha1(
            (
                profile
                + "\n__MDEXPLORE_RUST_PROFILE__\n"
                + prepared_source
                + "\n__MDEXPLORE_RUST_CFG__\n"
                + config_signature
            ).encode("utf-8", errors="replace")
        ).hexdigest()
        cached = self._mermaid_svg_cache.get(cache_key)
        if cached is not None:
            return cached, None

        tmp_input_path = None
        tmp_output_path = None
        tmp_config_path = None
        try:
            input_file = tempfile.NamedTemporaryFile("w", encoding="utf-8", suffix=".mmd", delete=False)
            tmp_input_path = Path(input_file.name)
            input_file.write(prepared_source)
            input_file.flush()
            input_file.close()

            output_file = tempfile.NamedTemporaryFile("w", encoding="utf-8", suffix=".svg", delete=False)
            tmp_output_path = Path(output_file.name)
            output_file.close()

            candidate_commands = []
            if profile == "preview":
                config_file = tempfile.NamedTemporaryFile("w", encoding="utf-8", suffix=".json", delete=False)
                tmp_config_path = Path(config_file.name)
                config_file.write(config_signature)
                config_file.flush()
                config_file.close()

                # `mmdr` CLI signatures vary by build. Prefer the current
                # flag-based form (-i/-o/-e), then fall back to positional.
                candidate_commands.extend(
                    [
                        [
                            str(self._mermaid_rs_binary),
                            "-i",
                            str(tmp_input_path),
                            "-o",
                            str(tmp_output_path),
                            "-e",
                            "svg",
                            "-c",
                            str(tmp_config_path),
                        ],
                        [
                            str(self._mermaid_rs_binary),
                            "-i",
                            str(tmp_input_path),
                            "-o",
                            str(tmp_output_path),
                            "-e",
                            "svg",
                        ],
                        [
                            str(self._mermaid_rs_binary),
                            str(tmp_input_path),
                            str(tmp_output_path),
                            "--output-format",
                            "svg",
                        ],
                    ]
                )
            else:
                candidate_commands.extend(
                    [
                        [
                            str(self._mermaid_rs_binary),
                            "-i",
                            str(tmp_input_path),
                            "-o",
                            str(tmp_output_path),
                            "-e",
                            "svg",
                        ],
                        [
                            str(self._mermaid_rs_binary),
                            str(tmp_input_path),
                            str(tmp_output_path),
                            "--output-format",
                            "svg",
                        ],
                    ]
                )
            result = None
            for command in candidate_commands:
                result = subprocess.run(
                    command,
                    text=True,
                    capture_output=True,
                    check=False,
                    timeout=20,
                )
                if result.returncode == 0:
                    break

            if result is None or result.returncode != 0:
                error_text = ((result.stderr if result is not None else "") or (result.stdout if result is not None else "") or "").strip()
                if not error_text:
                    code = result.returncode if result is not None else "unknown"
                    error_text = f"mmdr exited with code {code}"
                return None, error_text

            svg_markup = tmp_output_path.read_text(encoding="utf-8", errors="replace").strip()
            if "<svg" not in svg_markup.casefold():
                return None, "mmdr did not produce SVG output"
            cleaned_svg = (
                self._sanitize_rust_mermaid_svg_markup(svg_markup)
                if profile == "preview"
                else svg_markup
            )
            self._mermaid_svg_cache[cache_key] = cleaned_svg
            return cleaned_svg, None
        except subprocess.TimeoutExpired:
            return None, "mmdr render timed out"
        except Exception as exc:
            return None, f"Rust Mermaid render failed: {exc}"
        finally:
            if tmp_input_path is not None:
                try:
                    tmp_input_path.unlink(missing_ok=True)
                except Exception:
                    pass
            if tmp_output_path is not None:
                try:
                    tmp_output_path.unlink(missing_ok=True)
                except Exception:
                    pass
            if tmp_config_path is not None:
                try:
                    tmp_config_path.unlink(missing_ok=True)
                except Exception:
                    pass

    @staticmethod
    def _rust_mermaid_theme_config() -> dict[str, object]:
        """Dark-theme palette for Rust Mermaid output in GUI preview mode."""
        return {
            "theme": "base",
            "themeVariables": {
                "background": "#0f172a",
                "primaryColor": "#1e293b",
                "primaryBorderColor": "#93c5fd",
                "primaryTextColor": "#e5e7eb",
                "secondaryColor": "#172554",
                "tertiaryColor": "#111827",
                "lineColor": "#d1d5db",
                "textColor": "#e5e7eb",
                "edgeLabelBackground": "#0f172a",
                "clusterBkg": "#1f2937",
                "clusterBorder": "#94a3b8",
                "actorBkg": "#1e293b",
                "actorBorder": "#93c5fd",
                "actorLine": "#d1d5db",
                "noteBkg": "#1f2937",
                "noteBorderColor": "#93c5fd",
                "fontFamily": "Noto Sans, DejaVu Sans, sans-serif",
            },
        }

    @staticmethod
    def _parse_svg_length(value: str | None) -> float | None:
        """Parse numeric SVG lengths from values like '123', '123px', '123.4%'."""
        if not value:
            return None
        match = re.search(r"[-+]?\d*\.?\d+(?:[eE][-+]?\d+)?", str(value))
        if not match:
            return None
        try:
            return float(match.group(0))
        except Exception:
            return None

    @classmethod
    def _sanitize_rust_mermaid_svg_markup(cls, svg_markup: str) -> str:
        """Remove opaque white canvas background from Rust Mermaid SVG output."""
        if not svg_markup:
            return svg_markup
        try:
            root = ET.fromstring(svg_markup)
        except Exception:
            return svg_markup

        def local_name(tag: str) -> str:
            return tag.rsplit("}", 1)[-1] if "}" in tag else tag

        if local_name(root.tag).lower() != "svg":
            return svg_markup

        # Some renderers add root-level background styles; strip them for
        # dark preview transparency.
        style_attr = str(root.attrib.get("style", "")).strip()
        if style_attr:
            style_parts = [part.strip() for part in style_attr.split(";") if part.strip()]
            kept_parts = [part for part in style_parts if "background" not in part.casefold()]
            if kept_parts:
                root.set("style", "; ".join(kept_parts))
            else:
                root.attrib.pop("style", None)

        view_w = None
        view_h = None
        view_box = str(root.attrib.get("viewBox", "")).strip()
        if view_box:
            numbers = [float(part) for part in re.findall(r"[-+]?\d*\.?\d+(?:[eE][-+]?\d+)?", view_box)]
            if len(numbers) == 4:
                view_w = numbers[2]
                view_h = numbers[3]
        if view_w is None or view_h is None:
            view_w = cls._parse_svg_length(root.attrib.get("width"))
            view_h = cls._parse_svg_length(root.attrib.get("height"))

        white_fill_values = {
            "#fff",
            "#ffffff",
            "white",
            "rgb(255,255,255)",
            "rgba(255,255,255,1)",
            "rgba(255,255,255,1.0)",
        }

        # Rust output commonly injects a first full-canvas white <rect>.
        # Remove only when it clearly covers the canvas.
        for child in list(root):
            if local_name(child.tag).lower() != "rect":
                continue
            fill_value = str(child.attrib.get("fill", "")).strip().casefold().replace(" ", "")
            if not fill_value:
                style_text = str(child.attrib.get("style", ""))
                style_match = re.search(r"(?:^|;)\s*fill\s*:\s*([^;]+)", style_text, flags=re.IGNORECASE)
                if style_match:
                    fill_value = style_match.group(1).strip().casefold().replace(" ", "")
            if fill_value not in white_fill_values:
                continue

            x = cls._parse_svg_length(child.attrib.get("x")) or 0.0
            y = cls._parse_svg_length(child.attrib.get("y")) or 0.0
            w = cls._parse_svg_length(child.attrib.get("width"))
            h = cls._parse_svg_length(child.attrib.get("height"))
            if view_w and view_h and w and h:
                covers_canvas = x <= 1.0 and y <= 1.0 and w >= (view_w * 0.97) and h >= (view_h * 0.97)
            else:
                covers_canvas = x <= 1.0 and y <= 1.0
            if not covers_canvas:
                continue
            root.remove(child)
            break

        try:
            if root.tag.startswith("{") and "}" in root.tag:
                namespace_uri = root.tag[1:].split("}", 1)[0]
                ET.register_namespace("", namespace_uri)
            return ET.tostring(root, encoding="unicode")
        except Exception:
            return svg_markup

    def _resolve_local_mathjax_script(self) -> Path | None:
        """Locate a local MathJax bundle, preferring SVG output quality."""
        env_value = os.environ.get("MDEXPLORE_MATHJAX_JS", "").strip()
        candidates: list[Path] = []
        if env_value:
            candidates.append(Path(env_value).expanduser())

        app_dir = Path(__file__).resolve().parent
        candidates.extend(
            [
                app_dir / "mathjax" / "es5" / "tex-svg.js",
                app_dir / "mathjax" / "tex-svg.js",
                app_dir / "assets" / "mathjax" / "es5" / "tex-svg.js",
                app_dir / "vendor" / "mathjax" / "es5" / "tex-svg.js",
                Path("/usr/share/javascript/mathjax/es5/tex-svg.js"),
                Path("/usr/share/mathjax/es5/tex-svg.js"),
                Path("/usr/share/nodejs/mathjax/es5/tex-svg.js"),
                app_dir / "mathjax" / "es5" / "tex-mml-chtml.js",
                app_dir / "mathjax" / "tex-mml-chtml.js",
                app_dir / "assets" / "mathjax" / "es5" / "tex-mml-chtml.js",
                app_dir / "vendor" / "mathjax" / "es5" / "tex-mml-chtml.js",
                Path("/usr/share/javascript/mathjax/es5/tex-mml-chtml.js"),
                Path("/usr/share/mathjax/es5/tex-mml-chtml.js"),
                Path("/usr/share/nodejs/mathjax/es5/tex-mml-chtml.js"),
            ]
        )

        for candidate in candidates:
            try:
                if candidate.is_file():
                    return candidate.resolve()
            except Exception:
                continue
        return None

    def _mathjax_script_sources(self) -> list[str]:
        """Return local-first MathJax script URLs with CDN fallback."""
        sources: list[str] = []
        if self._mathjax_local_script is not None:
            try:
                sources.append(self._mathjax_local_script.as_uri())
            except Exception:
                pass
        # Prefer SVG output (closer to Obsidian quality), keep CHTML as fallback.
        sources.append("https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-svg.js")
        sources.append("https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js")
        # Keep order while dropping duplicates.
        return list(dict.fromkeys(sources))

    def _resolve_local_mermaid_script(self) -> Path | None:
        """Locate a local Mermaid bundle to use before CDN fallback."""
        env_value = os.environ.get("MDEXPLORE_MERMAID_JS", "").strip()
        candidates: list[Path] = []
        if env_value:
            candidates.append(Path(env_value).expanduser())

        app_dir = Path(__file__).resolve().parent
        candidates.extend(
            [
                app_dir / "mermaid" / "mermaid.min.js",
                app_dir / "mermaid" / "dist" / "mermaid.min.js",
                app_dir / "assets" / "mermaid" / "mermaid.min.js",
                app_dir / "assets" / "mermaid" / "dist" / "mermaid.min.js",
                app_dir / "vendor" / "mermaid" / "mermaid.min.js",
                app_dir / "vendor" / "mermaid" / "dist" / "mermaid.min.js",
                Path("/usr/share/javascript/mermaid/mermaid.min.js"),
                Path("/usr/share/nodejs/mermaid/dist/mermaid.min.js"),
            ]
        )

        for candidate in candidates:
            try:
                if candidate.is_file():
                    return candidate.resolve()
            except Exception:
                continue
        return None

    def _mermaid_script_sources(self) -> list[str]:
        """Return local-first Mermaid script URLs with CDN fallback."""
        sources: list[str] = []
        if self._mermaid_local_script is not None:
            try:
                sources.append(self._mermaid_local_script.as_uri())
            except Exception:
                pass
        sources.append("https://cdn.jsdelivr.net/npm/mermaid@11/dist/mermaid.min.js")
        # Keep order while dropping duplicates.
        return list(dict.fromkeys(sources))

    def _resolve_plantuml_jar_path(self) -> Path | None:
        """Locate plantuml.jar from env, vendor directory, app directory, or current directory."""
        env_value = os.environ.get("PLANTUML_JAR", "").strip()
        candidates: list[Path] = []
        if env_value:
            candidates.append(Path(env_value).expanduser())
        app_dir = Path(__file__).resolve().parent
        # Prefer the vendored jar location, but keep legacy fallbacks for compatibility.
        candidates.append(app_dir / "vendor" / "plantuml" / "plantuml.jar")
        candidates.append(app_dir / "plantuml.jar")
        candidates.append(Path.cwd() / "plantuml.jar")

        for candidate in candidates:
            try:
                if candidate.is_file():
                    return candidate.resolve()
            except Exception:
                continue
        return None

    def _plantuml_setup_error(self) -> str | None:
        """Return setup error text when local PlantUML execution is unavailable."""
        if self._plantuml_jar_path is None:
            return (
                "plantuml.jar not found "
                "(set PLANTUML_JAR or place jar at vendor/plantuml/plantuml.jar)"
            )
        if shutil.which("java") is None:
            return "Java runtime not found in PATH; install Java to render PlantUML diagrams"
        return None

    def _render_plantuml_data_uri(self, code: str) -> tuple[str | None, str | None]:
        """Render PlantUML source locally and return an SVG data URI."""
        prepared_code = self._prepare_plantuml_source(code)
        cache_key = hashlib.sha1(prepared_code.encode("utf-8", errors="replace")).hexdigest()
        cached = self._plantuml_svg_cache.get(cache_key)
        if cached is not None:
            return cached, None

        if self._plantuml_setup_issue is not None:
            return None, self._plantuml_setup_issue
        if self._plantuml_jar_path is None:
            return None, "plantuml.jar not available"

        command = [
            "java",
            "-Djava.awt.headless=true",
            "-jar",
            str(self._plantuml_jar_path),
            "-pipe",
            "-tsvg",
            "-charset",
            "UTF-8",
        ]

        try:
            result = subprocess.run(
                command,
                input=prepared_code,
                text=True,
                capture_output=True,
                check=False,
                timeout=20,
            )
        except subprocess.TimeoutExpired:
            return None, "Local PlantUML render timed out"
        except Exception as exc:
            return None, f"Local PlantUML render failed: {exc}"

        if result.returncode != 0:
            details = _extract_plantuml_error_details(result.stderr or "")
            return None, f"Local PlantUML render failed: {details}"

        svg_text = (result.stdout or "").strip()
        if "<svg" not in svg_text.casefold():
            return None, "Local PlantUML did not return SVG output"

        encoded_svg = base64.b64encode(svg_text.encode("utf-8")).decode("ascii")
        data_uri = f"data:image/svg+xml;base64,{encoded_svg}"
        self._plantuml_svg_cache[cache_key] = data_uri
        return data_uri, None

    @staticmethod
    def _prepare_plantuml_source(code: str) -> str:
        """Normalize PlantUML fence content for local jar rendering."""
        normalized = code.replace("\r\n", "\n").strip("\n")
        if not normalized:
            return "@startuml\n@enduml\n"

        has_start_directive = any(
            line.strip().casefold().startswith("@start")
            for line in normalized.splitlines()
            if line.strip()
        )
        if has_start_directive:
            return normalized + "\n"

        # Support shorthand fenced blocks that omit @startuml/@enduml.
        return f"@startuml\n{normalized}\n@enduml\n"

    @staticmethod
    def _prepare_mermaid_source(code: str) -> str:
        """Normalize Mermaid source for stable hashing/caching."""
        return code.replace("\r\n", "\n").strip("\n")

    def take_last_mermaid_pdf_svg_by_hash(self) -> dict[str, str]:
        """Return and clear PDF-mode Rust Mermaid SVG seed map for latest render."""
        payload = dict(self._last_mermaid_pdf_svg_by_hash)
        self._last_mermaid_pdf_svg_by_hash = {}
        return payload

    def render_document(
        self,
        markdown_text: str,
        title: str,
        total_lines: int | None = None,
        plantuml_resolver=None,
    ) -> str:
        # `env` is passed through markdown-it and lets fence renderers call back
        # into window-level async PlantUML orchestration when available.
        env = {}
        env["mermaid_index"] = 0
        env["mermaid_pdf_svg_by_hash"] = {}
        if callable(plantuml_resolver):
            env["plantuml_resolver"] = plantuml_resolver
            env["plantuml_index"] = 0
        body = self._md.render(markdown_text, env)
        if isinstance(env.get("mermaid_pdf_svg_by_hash"), dict):
            self._last_mermaid_pdf_svg_by_hash = dict(env.get("mermaid_pdf_svg_by_hash") or {})
        else:
            self._last_mermaid_pdf_svg_by_hash = {}
        escaped_title = html.escape(title)
        mermaid_cache_token = MERMAID_CACHE_JSON_TOKEN
        diagram_state_token = DIAGRAM_VIEW_STATE_JSON_TOKEN
        mathjax_sources_json = json.dumps(self._mathjax_script_sources())
        mermaid_sources_json = json.dumps(self._mermaid_script_sources())
        mermaid_backend_json = json.dumps(self._mermaid_backend)
        total_source_lines_json = json.dumps(max(1, int(total_lines or (markdown_text.count("\n") + 1))))
        return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8"/>
  <meta name="viewport" content="width=device-width, initial-scale=1"/>
  <title>{escaped_title}</title>
  <style>
    :root {{
      color-scheme: light dark;
      --fg: #1f2937;
      --bg: #f9fafb;
      --code-bg: #e5e7eb;
      --border: #d1d5db;
      --link: #0b57d0;
      --callout-note-border: #2563eb;
      --callout-note-bg: rgba(37, 99, 235, 0.12);
      --callout-tip-border: #16a34a;
      --callout-tip-bg: rgba(22, 163, 74, 0.12);
      --callout-important-border: #7c3aed;
      --callout-important-bg: rgba(124, 58, 237, 0.12);
      --callout-warning-border: #d97706;
      --callout-warning-bg: rgba(217, 119, 6, 0.14);
      --callout-caution-border: #dc2626;
      --callout-caution-bg: rgba(220, 38, 38, 0.12);
    }}
    @media (prefers-color-scheme: dark) {{
      :root {{
        --fg: #e5e7eb;
        --bg: #111827;
        --code-bg: #1f2937;
        --border: #374151;
        --link: #8ab4f8;
        --callout-note-border: #60a5fa;
        --callout-note-bg: rgba(96, 165, 250, 0.16);
        --callout-tip-border: #4ade80;
        --callout-tip-bg: rgba(74, 222, 128, 0.16);
        --callout-important-border: #a78bfa;
        --callout-important-bg: rgba(167, 139, 250, 0.18);
        --callout-warning-border: #fbbf24;
        --callout-warning-bg: rgba(251, 191, 36, 0.2);
        --callout-caution-border: #f87171;
        --callout-caution-bg: rgba(248, 113, 113, 0.18);
      }}
    }}
    html, body {{
      margin: 0;
      padding: 0;
      background: var(--bg);
      color: var(--fg);
      font-family: "Noto Sans", "DejaVu Sans", sans-serif;
      line-height: 1.55;
      font-size: 16px;
    }}
    main {{
      max-width: 980px;
      margin: 0 auto;
      padding: 1.1rem 1.4rem 4rem 1.4rem;
    }}
    a {{
      color: var(--link);
    }}
    pre, code {{
      font-family: "Noto Sans Mono", "DejaVu Sans Mono", monospace;
    }}
    code {{
      background: var(--code-bg);
      border-radius: 4px;
      padding: 0.1rem 0.35rem;
    }}
    pre {{
      background: var(--code-bg);
      border: 1px solid var(--border);
      border-radius: 6px;
      padding: 0.8rem;
      overflow: auto;
    }}
    pre > code {{
      background: transparent;
      padding: 0;
    }}
    table {{
      border-collapse: collapse;
    }}
    th, td {{
      border: 1px solid var(--border);
      padding: 0.4rem 0.6rem;
    }}
    .mermaid svg {{
      max-width: 100%;
      height: auto;
    }}
    .mdexplore-mermaid-shell {{
      margin: 0.65rem 0 0.95rem 0;
    }}
    .mdexplore-mermaid-toolbar {{
      display: flex;
      align-items: center;
      justify-content: flex-end;
      gap: 0.35rem;
      margin: 0 0 0.34rem 0;
    }}
    .mdexplore-mermaid-zoom-btn {{
      min-width: 1.9rem;
      height: 1.65rem;
      border: 1px solid var(--border);
      border-radius: 5px;
      background: var(--code-bg);
      color: var(--fg);
      font-size: 0.86rem;
      line-height: 1;
      font-weight: 600;
      cursor: pointer;
      user-select: none;
    }}
    .mdexplore-mermaid-zoom-btn:hover {{
      filter: brightness(1.07);
    }}
    .mdexplore-mermaid-zoom-value {{
      min-width: 3.6rem;
      text-align: center;
      font-size: 0.79rem;
      color: color-mix(in srgb, var(--fg) 86%, transparent);
      font-weight: 600;
      letter-spacing: 0.01em;
      user-select: none;
    }}
    .mdexplore-mermaid-viewport {{
      overflow: hidden;
      max-width: 100%;
      max-height: 78vh;
      border: 1px solid var(--border);
      border-radius: 8px;
      padding: 0.28rem;
      cursor: default;
    }}
    .mdexplore-mermaid-viewport.mdexplore-interaction-armed {{
      overflow: auto;
      cursor: grab;
    }}
    .mdexplore-mermaid-viewport.mdexplore-pan-active {{
      cursor: grabbing;
    }}
    .mdexplore-mermaid-viewport > svg {{
      display: block;
      transform-origin: top left;
      transform-box: fill-box;
      max-width: none !important;
      height: auto;
    }}
    @media screen and (prefers-color-scheme: dark) {{
      body:not(.mdexplore-pdf-export-mode) .mermaid .edge-thickness-normal,
      body:not(.mdexplore-pdf-export-mode) .mermaid .edge-thickness-thick,
      body:not(.mdexplore-pdf-export-mode) .mermaid .edge-pattern-solid,
      body:not(.mdexplore-pdf-export-mode) .mermaid .edge-pattern-dashed,
      body:not(.mdexplore-pdf-export-mode) .mermaid .edge-pattern-dotted,
      body:not(.mdexplore-pdf-export-mode) .mermaid .flowchart-link,
      body:not(.mdexplore-pdf-export-mode) .mermaid .relationshipLine,
      body:not(.mdexplore-pdf-export-mode) .mermaid .messageLine0,
      body:not(.mdexplore-pdf-export-mode) .mermaid .messageLine1,
      body:not(.mdexplore-pdf-export-mode) .mermaid .loopLine,
      body:not(.mdexplore-pdf-export-mode) .mermaid .activation0,
      body:not(.mdexplore-pdf-export-mode) .mermaid .activation1,
      body:not(.mdexplore-pdf-export-mode) .mermaid path[style*="stroke:#000"],
      body:not(.mdexplore-pdf-export-mode) .mermaid path[style*="stroke: #000"],
      body:not(.mdexplore-pdf-export-mode) .mermaid path[style*="stroke:black"],
      body:not(.mdexplore-pdf-export-mode) .mermaid path[style*="stroke: black"],
      body:not(.mdexplore-pdf-export-mode) .mermaid path[style*="fill:none"],
      body:not(.mdexplore-pdf-export-mode) .mermaid path[style*="fill: none"],
      body:not(.mdexplore-pdf-export-mode) .mermaid line[style*="stroke:#000"],
      body:not(.mdexplore-pdf-export-mode) .mermaid line[style*="stroke: #000"],
      body:not(.mdexplore-pdf-export-mode) .mermaid line[style*="stroke:black"],
      body:not(.mdexplore-pdf-export-mode) .mermaid line[style*="stroke: black"],
      body:not(.mdexplore-pdf-export-mode) .mermaid line[style*="fill:none"],
      body:not(.mdexplore-pdf-export-mode) .mermaid line[style*="fill: none"],
      body:not(.mdexplore-pdf-export-mode) .mermaid polyline[style*="fill:none"],
      body:not(.mdexplore-pdf-export-mode) .mermaid polyline[style*="fill: none"] {{
        stroke: #eaf2ff !important;
        stroke-opacity: 1 !important;
        opacity: 1 !important;
      }}
      body:not(.mdexplore-pdf-export-mode) .mermaid .marker,
      body:not(.mdexplore-pdf-export-mode) .mermaid .marker path,
      body:not(.mdexplore-pdf-export-mode) .mermaid marker path {{
        stroke: #eaf2ff !important;
        fill: #eaf2ff !important;
        stroke-opacity: 1 !important;
        fill-opacity: 1 !important;
        opacity: 1 !important;
      }}
      body:not(.mdexplore-pdf-export-mode) .mermaid g.edgeLabel,
      body:not(.mdexplore-pdf-export-mode) .mermaid g.edgeLabel *,
      body:not(.mdexplore-pdf-export-mode) .mermaid .messageText,
      body:not(.mdexplore-pdf-export-mode) .mermaid .messageText *,
      body:not(.mdexplore-pdf-export-mode) .mermaid .relation,
      body:not(.mdexplore-pdf-export-mode) .mermaid .relation *,
      body:not(.mdexplore-pdf-export-mode) .mermaid [class*="edgeLabel"] text,
      body:not(.mdexplore-pdf-export-mode) .mermaid [class*="edgeLabel"] tspan {{
        color: #ffffff !important;
        fill: #ffffff !important;
        opacity: 1 !important;
      }}
      body:not(.mdexplore-pdf-export-mode) .mermaid .labelBkg,
      body:not(.mdexplore-pdf-export-mode) .mermaid .edgeLabel rect,
      body:not(.mdexplore-pdf-export-mode) .mermaid rect.edgeLabel,
      body:not(.mdexplore-pdf-export-mode) .mermaid rect.sequenceEdgeLabel,
      body:not(.mdexplore-pdf-export-mode) .mermaid rect[class*="edgeLabel"] {{
        fill: #1e293b !important;
        stroke: #93c5fd !important;
      }}
      body:not(.mdexplore-pdf-export-mode) .mermaid rect[stroke-dasharray][fill="none"] {{
        stroke: #c3d4ef !important;
        stroke-opacity: 0.96 !important;
      }}
      body:not(.mdexplore-pdf-export-mode) .mermaid g.row-rect-even > path:first-child {{
        fill: #2b3f5f !important;
      }}
      body:not(.mdexplore-pdf-export-mode) .mermaid g.row-rect-odd > path:first-child {{
        fill: #223754 !important;
      }}
      body:not(.mdexplore-pdf-export-mode) .mermaid g.row-rect-even > path,
      body:not(.mdexplore-pdf-export-mode) .mermaid g.row-rect-odd > path {{
        stroke: #93c5fd !important;
      }}
      body:not(.mdexplore-pdf-export-mode) .mermaid g.label.name .nodeLabel,
      body:not(.mdexplore-pdf-export-mode) .mermaid g.label.attribute-type .nodeLabel,
      body:not(.mdexplore-pdf-export-mode) .mermaid g.label.attribute-name .nodeLabel,
      body:not(.mdexplore-pdf-export-mode) .mermaid g.label.attribute-keys .nodeLabel,
      body:not(.mdexplore-pdf-export-mode) .mermaid g.label.attribute-comment .nodeLabel,
      body:not(.mdexplore-pdf-export-mode) .mermaid g.label.name text,
      body:not(.mdexplore-pdf-export-mode) .mermaid g.label.attribute-type text,
      body:not(.mdexplore-pdf-export-mode) .mermaid g.label.attribute-name text,
      body:not(.mdexplore-pdf-export-mode) .mermaid g.label.attribute-keys text,
      body:not(.mdexplore-pdf-export-mode) .mermaid g.label.attribute-comment text {{
        color: #e5e7eb !important;
        fill: #e5e7eb !important;
        opacity: 1 !important;
      }}
    }}
    .mermaid-pending {{
      margin: 0.8rem 0;
      padding: 0.55rem 0.7rem;
      border: 1px dashed var(--border);
      border-radius: 6px;
      font-style: italic;
      opacity: 0.9;
    }}
    img.plantuml {{
      display: block;
      max-width: 100%;
      margin: 0.8rem 0;
      border: 1px solid var(--border);
      border-radius: 6px;
      background: #fff;
    }}
    main img:not(.plantuml) {{
      max-width: 100%;
      width: auto;
      height: auto;
    }}
    .plantuml-error-message {{
      margin: 0.8rem 0 0.4rem 0;
      color: #b91c1c;
      font-weight: 600;
    }}
    pre.plantuml-error-detail {{
      margin: 0 0 0.8rem 0;
      white-space: pre-wrap;
      word-break: break-word;
      color: #b91c1c;
      background: color-mix(in srgb, var(--bg) 85%, #ef4444 15%);
      border: 1px solid #ef9a9a;
      border-radius: 6px;
      padding: 0.55rem 0.7rem;
      font-size: 0.92rem;
    }}
    .plantuml-pending {{
      margin: 0.8rem 0;
      padding: 0.55rem 0.7rem;
      border: 1px dashed var(--border);
      border-radius: 6px;
      font-style: italic;
      opacity: 0.9;
    }}
    .mdexplore-callout {{
      margin: 0.9rem 0;
      padding: 0.72rem 0.9rem 0.78rem 0.95rem;
      border-left: 0.32rem solid var(--callout-note-border);
      background: var(--callout-note-bg);
      border-radius: 0.45rem;
      break-inside: avoid;
      page-break-inside: avoid;
    }}
    .mdexplore-callout-title {{
      display: flex;
      align-items: center;
      gap: 0.5rem;
      margin: 0 0 0.38rem 0;
      font-weight: 700;
      letter-spacing: 0.01em;
    }}
    .mdexplore-callout-icon {{
      display: inline-flex;
      align-items: center;
      justify-content: center;
      width: 1.05rem;
      height: 1.05rem;
      border-radius: 999px;
      border: 1px solid currentColor;
      font-size: 0.73rem;
      line-height: 1;
      font-family: "Noto Sans", "DejaVu Sans", sans-serif;
      font-weight: 700;
      flex: 0 0 auto;
    }}
    .mdexplore-callout-content > :first-child {{
      margin-top: 0;
    }}
    .mdexplore-callout-content > :last-child {{
      margin-bottom: 0;
    }}
    .mdexplore-callout-note {{
      border-left-color: var(--callout-note-border);
      background: var(--callout-note-bg);
    }}
    .mdexplore-callout-tip {{
      border-left-color: var(--callout-tip-border);
      background: var(--callout-tip-bg);
    }}
    .mdexplore-callout-important {{
      border-left-color: var(--callout-important-border);
      background: var(--callout-important-bg);
    }}
    .mdexplore-callout-warning {{
      border-left-color: var(--callout-warning-border);
      background: var(--callout-warning-bg);
    }}
    .mdexplore-callout-caution {{
      border-left-color: var(--callout-caution-border);
      background: var(--callout-caution-bg);
    }}
    .mdexplore-scroll-line-indicator {{
      position: fixed;
      left: 0;
      top: 18px;
      z-index: 2147483647;
      display: none;
      pointer-events: none;
      padding: 0.2rem 0.48rem;
      border: 1px solid color-mix(in srgb, var(--border) 78%, transparent);
      border-radius: 999px;
      background: color-mix(in srgb, var(--bg) 88%, transparent);
      color: var(--fg);
      font-family: "Noto Sans Mono", "DejaVu Sans Mono", monospace;
      font-size: 0.76rem;
      font-weight: 700;
      line-height: 1.2;
      white-space: nowrap;
      box-shadow: 0 6px 18px rgba(15, 23, 42, 0.18);
      transform: translateY(-50%);
      opacity: 0;
      transition: opacity 90ms ease-out;
    }}
    .mdexplore-scroll-line-indicator.mdexplore-visible {{
      display: block;
      opacity: 1;
    }}
    .mdexplore-scroll-hit-overlay {{
      position: fixed;
      top: 0;
      left: 0;
      width: 15px;
      height: 100vh;
      display: none;
      pointer-events: auto;
      z-index: 2147483646;
    }}
    .mdexplore-scroll-hit-overlay.mdexplore-visible {{
      display: block;
    }}
    .mdexplore-scroll-hit-marker {{
      position: absolute;
      left: 0;
      width: 100%;
      min-height: 5px;
      border-radius: 999px;
      pointer-events: auto;
      cursor: pointer;
      background: #f7dc63;
      box-shadow: 0 0 0 1px rgba(17, 24, 39, 0.28);
      opacity: 0.98;
      user-select: none;
      touch-action: none;
    }}
    .mdexplore-scroll-hit-marker:hover {{
      background: #fde68a;
    }}
    @media print {{
      .mdexplore-scroll-line-indicator {{
        display: none !important;
      }}
      .mdexplore-scroll-hit-overlay {{
        display: none !important;
      }}
      .mdexplore-mermaid-toolbar {{
        display: none !important;
      }}
      .mdexplore-mermaid-viewport {{
        border: none !important;
        border-radius: 0 !important;
        padding: 0 !important;
        max-height: none !important;
        overflow: visible !important;
      }}
      .mdexplore-mermaid-viewport > svg {{
        transform: none !important;
        max-width: 100% !important;
        width: auto !important;
      }}
      .mdexplore-callout {{
        border-left-width: 4px;
      }}
    }}
    mjx-container[display="true"] {{
      margin: 0.9em 0 1.05em 0 !important;
    }}
    mjx-container[jax="SVG"] {{
      font-size: 1.07em;
    }}
    mjx-container[jax="SVG"] > svg {{
      max-width: 100%;
      height: auto;
      overflow: visible;
    }}
    mjx-container[jax="SVG"][display="false"] {{
      vertical-align: -0.08em;
    }}
  </style>
  <script>
    // Preview bootstrap state shared across Python -> JS round-trips. Python
    // seeds caches and persisted diagram viewport state into the page so GUI
    // restores and PDF export can reuse the same rendered artifacts.
    window.MathJax = {{
      startup: {{
        typeset: false
      }},
      tex: {{
        inlineMath: [['$', '$'], ['\\\\(', '\\\\)']],
        displayMath: [['$$', '$$'], ['\\\\[', '\\\\]']]
      }},
      svg: {{
        fontCache: "global",
        scale: 1.05
      }},
      chtml: {{
        scale: 1.05,
        matchFontHeight: false
      }},
      options: {{
        skipHtmlTags: ['script', 'noscript', 'style', 'textarea', 'pre', 'code']
      }}
    }};
    window.__mdexploreMathReady = false;
    window.__mdexploreMathInFlight = false;
    window.__mdexploreMathJaxSource = "";
    window.__mdexploreMathJaxSources = {mathjax_sources_json};
    window.__mdexploreMathJaxLoadPromise = null;
    window.__mdexploreMermaidReady = false;
    window.__mdexploreMermaidSource = "";
    window.__mdexploreMermaidSources = {mermaid_sources_json};
    window.__mdexploreMermaidBackend = {mermaid_backend_json};
    window.__mdexploreSourceTotalLines = {total_source_lines_json};
    window.__mdexploreMermaidLoadPromise = null;
    window.__mdexploreMermaidAttempted = false;
    window.__mdexploreMermaidPaletteMode = "auto";
    window.__mdexploreMermaidRenderPromise = null;
    window.__mdexploreMermaidRenderMode = "";
    window.__mdexploreMermaidSvgCacheByMode = (() => {{
      try {{
        const seedText = {json.dumps(mermaid_cache_token)};
        const parsed = JSON.parse(seedText);
        if (parsed && typeof parsed === "object") {{
          return parsed;
        }}
      }} catch (_error) {{
        // Seed parsing is best-effort.
      }}
      return {{}};
    }})();
    window.__mdexploreDiagramViewState = (() => {{
      try {{
        const seedText = {json.dumps(diagram_state_token)};
        const parsed = JSON.parse(seedText);
        if (parsed && typeof parsed === "object") {{
          return parsed;
        }}
      }} catch (_error) {{
        // Seed parsing is best-effort.
      }}
      return {{}};
    }})();
    window.__mdexploreGetDiagramViewState = (stateKey) => {{
      // Return a normalized diagram state payload; callers rely on finite
      // numbers here because the result may be persisted back to Python.
      const key = String(stateKey || "").trim();
      if (!key) {{
        return null;
      }}
      const all = window.__mdexploreDiagramViewState;
      if (!all || typeof all !== "object") {{
        return null;
      }}
      const raw = all[key];
      if (!raw || typeof raw !== "object") {{
        return null;
      }}
      const zoom = Number(raw.zoom);
      const scrollLeft = Number(raw.scrollLeft);
      const scrollTop = Number(raw.scrollTop);
      return {{
        zoom: Number.isFinite(zoom) ? zoom : 1.0,
        scrollLeft: Number.isFinite(scrollLeft) ? scrollLeft : 0,
        scrollTop: Number.isFinite(scrollTop) ? scrollTop : 0,
        dirty: !!raw.dirty,
      }};
    }};
    window.__mdexploreSetDiagramViewState = (stateKey, rawState) => {{
      // Diagram zoom/pan is stored per-hash/per-index so view tabs for the same
      // document can restore independent scroll positions.
      const key = String(stateKey || "").trim();
      if (!key) {{
        return;
      }}
      if (!window.__mdexploreDiagramViewState || typeof window.__mdexploreDiagramViewState !== "object") {{
        window.__mdexploreDiagramViewState = {{}};
      }}
      const zoom = Number(rawState && rawState.zoom);
      const scrollLeft = Number(rawState && rawState.scrollLeft);
      const scrollTop = Number(rawState && rawState.scrollTop);
      window.__mdexploreDiagramViewState[key] = {{
        zoom: Number.isFinite(zoom) ? zoom : 1.0,
        scrollLeft: Number.isFinite(scrollLeft) ? scrollLeft : 0.0,
        scrollTop: Number.isFinite(scrollTop) ? scrollTop : 0.0,
        dirty: !!(rawState && rawState.dirty),
      }};
    }};
    window.__mdexploreCollectDiagramViewState = () => {{
      // Called from Python before document switches and PDF export. The result
      // becomes the persisted in-memory diagram-state map for the current run.
      const source = window.__mdexploreDiagramViewState;
      if (!source || typeof source !== "object") {{
        return {{}};
      }}
      const out = {{}};
      for (const [rawKey, rawValue] of Object.entries(source)) {{
        const key = String(rawKey || "").trim();
        if (!key || key.length > 240) {{
          continue;
        }}
        const parsed = window.__mdexploreGetDiagramViewState(key);
        if (!parsed) {{
          continue;
        }}
        out[key] = parsed;
      }}
      return out;
    }};

    window.__mdexploreLoadMathJaxScript = () => {{
      // MathJax and Mermaid both use local-first fallback chains because the
      // app must work offline when vendor assets are present but still recover
      // gracefully with CDN sources when they are not.
      if (window.__mdexploreMathJaxLoadPromise) {{
        return window.__mdexploreMathJaxLoadPromise;
      }}
      window.__mdexploreMathJaxLoadPromise = (async () => {{
        const sources = Array.isArray(window.__mdexploreMathJaxSources) ? window.__mdexploreMathJaxSources : [];
        for (const src of sources) {{
          try {{
            await new Promise((resolve, reject) => {{
              const script = document.createElement("script");
              script.src = src;
              script.defer = true;
              script.onload = () => resolve(true);
              script.onerror = () => reject(new Error(`Failed to load ${{src}}`));
              document.head.appendChild(script);
            }});
            if (window.MathJax && MathJax.typesetPromise) {{
              window.__mdexploreMathJaxSource = src;
              return true;
            }}
          }} catch (error) {{
            console.error("mdexplore MathJax script load failed:", src, error);
          }}
        }}
        return false;
      }})();
      return window.__mdexploreMathJaxLoadPromise;
    }};

    window.__mdexploreLoadMermaidScript = () => {{
      if (window.__mdexploreMermaidLoadPromise) {{
        return window.__mdexploreMermaidLoadPromise;
      }}
      window.__mdexploreMermaidLoadPromise = (async () => {{
        const sources = Array.isArray(window.__mdexploreMermaidSources) ? window.__mdexploreMermaidSources : [];
        for (const src of sources) {{
          try {{
            await new Promise((resolve, reject) => {{
              const script = document.createElement("script");
              script.src = src;
              script.defer = true;
              script.onload = () => resolve(true);
              script.onerror = () => reject(new Error(`Failed to load ${{src}}`));
              document.head.appendChild(script);
            }});
            if (window.mermaid) {{
              window.__mdexploreMermaidSource = src;
              return true;
            }}
          }} catch (error) {{
            console.error("mdexplore Mermaid script load failed:", src, error);
          }}
        }}
        return false;
      }})();
      return window.__mdexploreMermaidLoadPromise;
    }};

    window.__mdexploreClearPdfExportMode = () => {{
      // PDF export temporarily mutates DOM/theme state. Always provide a
      // single cleanup entry point so post-export GUI restore is predictable.
      try {{
        if (document.documentElement) {{
          document.documentElement.classList.remove("mdexplore-pdf-export-mode");
        }}
        if (document.body) {{
          document.body.classList.remove("mdexplore-pdf-export-mode");
        }}
        const pdfMermaidOverride = document.getElementById("__mdexplore_pdf_mermaid_light_override");
        if (pdfMermaidOverride && pdfMermaidOverride.parentNode) {{
          pdfMermaidOverride.parentNode.removeChild(pdfMermaidOverride);
        }}
      }} catch (_error) {{
        // Best-effort cleanup only.
      }}
    }};

    window.__mdexploreParseCssRgb = (colorText) => {{
      const text = String(colorText || "").trim();
      const match = text.match(/^rgba?\\(([^)]+)\\)$/i);
      if (!match) {{
        return null;
      }}
      const parts = match[1].split(",").map((part) => Number.parseFloat(part.trim()));
      if (parts.length < 3 || parts.some((value) => Number.isNaN(value))) {{
        return null;
      }}
      return [parts[0], parts[1], parts[2]];
    }};

    window.__mdexploreIsDarkBackground = () => {{
      try {{
        const body = document.body || document.documentElement;
        if (!body) {{
          return true;
        }}
        const bg = getComputedStyle(body).backgroundColor || "";
        const rgb = window.__mdexploreParseCssRgb(bg);
        if (rgb) {{
          const [r, g, b] = rgb.map((value) => Math.max(0, Math.min(255, value)) / 255);
          const luminance = (0.2126 * r) + (0.7152 * g) + (0.0722 * b);
          return luminance < 0.56;
        }}
      }} catch (_error) {{
        // Fall through to media query fallback.
      }}
      return !!(window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches);
    }};

    window.__mdexploreApproxTopVisibleLine = () => {{
      // Approximate the source line nearest the top of the viewport using the
      // source-line tags injected by MarkdownRenderer.
      const probeX = Math.max(14, Math.floor(window.innerWidth * 0.42));
      const probeYs = [10, 20, 34, 50, 72, 96];
      for (const y of probeYs) {{
        const el = document.elementFromPoint(probeX, y);
        if (!el) continue;
        const tagged = el.closest('[data-md-line-start]');
        if (!tagged) continue;
        const value = parseInt(tagged.getAttribute('data-md-line-start') || "", 10);
        if (!Number.isNaN(value)) return value + 1;
      }}
      const taggedNodes = document.querySelectorAll('[data-md-line-start]');
      for (const node of taggedNodes) {{
        const rect = node.getBoundingClientRect();
        if (rect.bottom < 0) continue;
        const value = parseInt(node.getAttribute('data-md-line-start') || "", 10);
        if (!Number.isNaN(value)) return value + 1;
      }}
      return 1;
    }};

    window.__mdexploreInstallScrollLineIndicator = () => {{
      // This installs both scrollbar-adjacent UI features:
      // 1. live "current / total" line indicator while dragging the scrollbar
      // 2. yellow search-hit markers that can be clicked to jump within a doc
      if (window.__mdexploreScrollLineIndicatorInstalled) {{
        return;
      }}
      window.__mdexploreScrollLineIndicatorInstalled = true;

      const indicator = document.createElement("div");
      indicator.className = "mdexplore-scroll-line-indicator";
      document.body.appendChild(indicator);
      const hitOverlay = document.createElement("div");
      hitOverlay.className = "mdexplore-scroll-hit-overlay";
      document.body.appendChild(hitOverlay);

      const state = {{
        pointerX: window.innerWidth,
        pointerY: 0,
        leftMouseDown: false,
        active: false,
        hideTimer: null,
        searchRefreshTimer: null,
      }};

      const clearHideTimer = () => {{
        if (state.hideTimer) {{
          window.clearTimeout(state.hideTimer);
          state.hideTimer = null;
        }}
      }};

      const viewportScrollableHeight = () =>
        Math.max(
          0,
          (document.documentElement ? document.documentElement.scrollHeight : 0) - window.innerHeight
        );

      const scrollbarWidth = () => {{
        const doc = document.documentElement;
        return Math.max(0, window.innerWidth - (doc ? doc.clientWidth : window.innerWidth));
      }};

      const syncOverlayHorizontalPosition = () => {{
        const docClientWidth = document.documentElement ? document.documentElement.clientWidth : window.innerWidth;
        const gap = 0;
        const overlayWidth = Math.max(4, hitOverlay.offsetWidth || 6);
        const overlayLeft = Math.max(0, docClientWidth - overlayWidth - gap);
        hitOverlay.style.left = `${{Math.round(overlayLeft)}}px`;
      }};

      const isNearVerticalScrollbar = () => {{
        const width = Math.max(12, scrollbarWidth());
        return state.pointerX >= window.innerWidth - width - 10;
      }};

      const updateIndicator = () => {{
        // The indicator is positioned from the actual scrollbar/viewport
        // geometry rather than from guessed margins so it tracks the handle.
        if (!indicator.isConnected) {{
          return;
        }}
        const totalLines = Math.max(1, Number(window.__mdexploreSourceTotalLines || 1));
        const currentLine = Math.max(1, Math.min(totalLines, Number(window.__mdexploreApproxTopVisibleLine() || 1)));
        indicator.textContent = `${{currentLine}} / ${{totalLines}}`;

        const scrollable = viewportScrollableHeight();
        const trackTop = 0;
        const trackHeight = window.innerHeight;
        let handleHeight = trackHeight;
        let handleTop = trackTop;
        if (scrollable > 0) {{
          const visibleRatio = Math.max(0.06, Math.min(1, window.innerHeight / (scrollable + window.innerHeight)));
          handleHeight = Math.max(26, Math.round(trackHeight * visibleRatio));
          const handleTravel = Math.max(0, trackHeight - handleHeight);
          const progress = Math.max(0, Math.min(1, window.scrollY / scrollable));
          handleTop = trackTop + (handleTravel * progress);
        }}
        const handleCenterY = Math.max(
          20,
          Math.min(window.innerHeight - 20, handleTop + (handleHeight / 2))
        );
        const docClientWidth = document.documentElement ? document.documentElement.clientWidth : window.innerWidth;
        const gap = 4;
        const indicatorWidth = Math.max(1, indicator.offsetWidth || 0);
        const indicatorLeft = Math.max(
          4,
          docClientWidth - Math.max(0, scrollbarWidth()) - indicatorWidth - gap
        );
        indicator.style.top = `${{Math.round(handleCenterY)}}px`;
        indicator.style.left = `${{Math.round(indicatorLeft)}}px`;
        syncOverlayHorizontalPosition();
      }};

      const jumpToTarget = (target) => {{
        if (!target || typeof target.getBoundingClientRect !== "function") {{
          return;
        }}
        const rect = target.getBoundingClientRect();
        const absoluteTop = window.scrollY + rect.top;
        const targetCenter = absoluteTop + Math.max(0, rect.height * 0.5);
        const desiredTop = Math.max(0, targetCenter - (window.innerHeight * 0.5));
        window.scrollTo({{
          top: desiredTop,
          behavior: "auto",
        }});
      }};

      const refreshSearchHitMarkers = () => {{
        // Build a compact map of highlighted search results along the document
        // height. Nearby hits are merged into clusters to avoid a solid strip.
        if (!hitOverlay.isConnected) {{
          return;
        }}
        hitOverlay.replaceChildren();
        const marks = Array.from(document.querySelectorAll('[data-mdexplore-search-mark="1"]'));
        const scrollHeight = Math.max(
          1,
          document.documentElement ? document.documentElement.scrollHeight : 0,
          document.body ? document.body.scrollHeight : 0
        );
        if (!marks.length || scrollHeight <= window.innerHeight) {{
          hitOverlay.classList.remove("mdexplore-visible");
          syncOverlayHorizontalPosition();
          return;
        }}

        const trackHeight = window.innerHeight;
        const markerPositions = [];
        for (const mark of marks) {{
          const rect = mark.getBoundingClientRect();
          if (!rect || rect.height <= 0) {{
            continue;
          }}
          const absoluteTop = window.scrollY + rect.top;
          const absoluteBottom = absoluteTop + rect.height;
          const topPx = Math.max(0, Math.min(trackHeight - 4, (absoluteTop / scrollHeight) * trackHeight));
          const bottomPx = Math.max(topPx + 3, Math.min(trackHeight, (absoluteBottom / scrollHeight) * trackHeight));
          const centerPx = Math.max(topPx, Math.min(bottomPx, ((absoluteTop + absoluteBottom) * 0.5 / scrollHeight) * trackHeight));
          markerPositions.push({{
            top: topPx,
            bottom: bottomPx,
            target: mark,
            center: centerPx,
          }});
        }}

        if (!markerPositions.length) {{
          hitOverlay.classList.remove("mdexplore-visible");
          syncOverlayHorizontalPosition();
          return;
        }}

        markerPositions.sort((a, b) => a.top - b.top);
        const merged = [];
        for (const item of markerPositions) {{
          const top = Math.round(item.top);
          const bottom = Math.round(item.bottom);
          const previous = merged.length ? merged[merged.length - 1] : null;
          if (previous && top <= previous.bottom + 2) {{
            previous.bottom = Math.max(previous.bottom, bottom);
            previous.targets.push({{
              element: item.target,
              center: item.center,
            }});
            continue;
          }}
          merged.push({{
            top,
            bottom,
            targets: [{{
              element: item.target,
              center: item.center,
            }}],
          }});
        }}

        for (const item of merged) {{
          const marker = document.createElement("div");
          marker.className = "mdexplore-scroll-hit-marker";
          marker.style.top = `${{item.top}}px`;
          marker.style.height = `${{Math.max(5, item.bottom - item.top)}}px`;
          const activateMarker = (event) => {{
            if (typeof event.button === "number" && event.button !== 0) {{
              return;
            }}
            event.preventDefault();
            event.stopPropagation();
            if (typeof event.stopImmediatePropagation === "function") {{
              event.stopImmediatePropagation();
            }}
            const clickY = Number.isFinite(event.clientY) ? event.clientY : (item.top + item.bottom) * 0.5;
            const targetInfo = Array.isArray(item.targets) && item.targets.length
              ? item.targets.reduce((best, candidate) => {{
                  if (!best) return candidate;
                  return Math.abs(candidate.center - clickY) < Math.abs(best.center - clickY) ? candidate : best;
                }}, null)
              : null;
            const target = targetInfo && targetInfo.element ? targetInfo.element : null;
            if (!target) {{
              return;
            }}
            jumpToTarget(target);
          }};
          marker.addEventListener("mousedown", activateMarker);
          marker.addEventListener("pointerdown", activateMarker);
          hitOverlay.appendChild(marker);
        }}
        syncOverlayHorizontalPosition();
        hitOverlay.classList.add("mdexplore-visible");
      }};

      const scheduleSearchHitRefresh = (delayMs = 40) => {{
        if (state.searchRefreshTimer) {{
          window.clearTimeout(state.searchRefreshTimer);
        }}
        state.searchRefreshTimer = window.setTimeout(() => {{
          state.searchRefreshTimer = null;
          refreshSearchHitMarkers();
        }}, delayMs);
      }};

      window.__mdexploreRefreshScrollHitMarkers = () => {{
        scheduleSearchHitRefresh(0);
      }};

      const showIndicator = () => {{
        clearHideTimer();
        updateIndicator();
        indicator.classList.add("mdexplore-visible");
      }};

      const hideIndicatorSoon = (delayMs = 150) => {{
        clearHideTimer();
        state.hideTimer = window.setTimeout(() => {{
          state.active = false;
          indicator.classList.remove("mdexplore-visible");
        }}, delayMs);
      }};

      const trackPointer = (event) => {{
        if (!event) {{
          return;
        }}
        if (Number.isFinite(event.clientX)) {{
          state.pointerX = event.clientX;
        }}
        if (Number.isFinite(event.clientY)) {{
          state.pointerY = event.clientY;
        }}
        if (typeof event.buttons === "number") {{
          state.leftMouseDown = (event.buttons & 1) === 1;
        }}
      }};

      window.addEventListener("mousemove", (event) => {{
        trackPointer(event);
        if (state.active) {{
          updateIndicator();
        }}
      }}, {{ passive: true }});

      window.addEventListener("mousedown", (event) => {{
        trackPointer(event);
        if (event.button !== 0) {{
          return;
        }}
        state.leftMouseDown = true;
        if (viewportScrollableHeight() <= 0) {{
          return;
        }}
        if (isNearVerticalScrollbar()) {{
          state.active = true;
          showIndicator();
        }}
      }}, {{ passive: true }});

      window.addEventListener("mouseup", () => {{
        state.leftMouseDown = false;
        if (state.active) {{
          hideIndicatorSoon(120);
        }}
      }}, {{ passive: true }});

      window.addEventListener("blur", () => {{
        state.leftMouseDown = false;
        state.active = false;
        clearHideTimer();
        indicator.classList.remove("mdexplore-visible");
      }});

      window.addEventListener("scroll", () => {{
        if (viewportScrollableHeight() <= 0) {{
          state.active = false;
          indicator.classList.remove("mdexplore-visible");
          hitOverlay.classList.remove("mdexplore-visible");
          return;
        }}
        if (state.active || (state.leftMouseDown && isNearVerticalScrollbar())) {{
          state.active = true;
          showIndicator();
          if (!state.leftMouseDown) {{
            hideIndicatorSoon(140);
          }}
        }}
      }}, {{ passive: true }});

      window.addEventListener("resize", () => {{
        if (state.active) {{
          updateIndicator();
        }}
        scheduleSearchHitRefresh(0);
      }}, {{ passive: true }});

      const searchObserver = new MutationObserver((mutationList) => {{
        for (const mutation of mutationList) {{
          if (mutation.type === "childList" || mutation.type === "attributes") {{
            scheduleSearchHitRefresh();
            return;
          }}
        }}
      }});
      searchObserver.observe(document.body, {{
        subtree: true,
        childList: true,
        attributes: true,
        attributeFilter: ["data-mdexplore-search-mark"],
      }});

      scheduleSearchHitRefresh(0);
    }};

    window.__mdexploreMermaidInitConfig = (mode = "auto") => {{
      // Mermaid is configured twice: an interactive preview palette and a
      // deliberately plain PDF palette. The PDF path is later normalized to
      // grayscale/print-safe contrast and must not inherit preview tuning.
      const usePdfMode = String(mode || "").toLowerCase() === "pdf";
      const dark = !usePdfMode && window.__mdexploreIsDarkBackground();
      const shared = {{
        startOnLoad: false,
        securityLevel: "loose",
        fontFamily: "Noto Sans, DejaVu Sans, sans-serif",
        flowchart: {{ htmlLabels: true, useMaxWidth: true }},
        sequence: {{ useMaxWidth: true }},
        gantt: {{ useMaxWidth: true }},
      }};

      if (usePdfMode) {{
        return {{
          ...shared,
          // Keep PDF Mermaid rendering "vanilla" (no mdexplore color tuning).
          theme: "default",
          darkMode: false,
        }};
      }}

      if (dark) {{
        return {{
          ...shared,
          theme: "base",
          darkMode: true,
          themeVariables: {{
            background: "#0f172a",
            primaryColor: "#1e293b",
            primaryBorderColor: "#93c5fd",
            primaryTextColor: "#e5e7eb",
            secondaryColor: "#172554",
            secondaryBorderColor: "#93c5fd",
            secondaryTextColor: "#e5e7eb",
            tertiaryColor: "#111827",
            tertiaryBorderColor: "#94a3b8",
            tertiaryTextColor: "#e5e7eb",
            lineColor: "#d1d5db",
            textColor: "#e5e7eb",
            mainBkg: "#1e293b",
            nodeBkg: "#1e293b",
            clusterBkg: "#1f2937",
            clusterBorder: "#94a3b8",
            edgeLabelBackground: "#0f172a",
            titleColor: "#e5e7eb",
            actorBkg: "#1e293b",
            actorBorder: "#93c5fd",
            actorTextColor: "#e5e7eb",
            actorLineColor: "#d1d5db",
            signalColor: "#d1d5db",
            noteBkgColor: "#1f2937",
            noteTextColor: "#e5e7eb",
            noteBorderColor: "#93c5fd",
            attributeBackgroundColorOdd: "#2b3f5f",
            attributeBackgroundColorEven: "#223754",
            labelTextColor: "#e5e7eb",
            cScale0: "#60a5fa",
            cScale1: "#93c5fd",
            cScale2: "#bfdbfe",
            cScale3: "#e2e8f0",
            cScale4: "#cbd5e1",
            cScale5: "#94a3b8",
            cScale6: "#64748b",
            cScale7: "#475569",
            cScale8: "#334155",
            cScale9: "#1f2937",
          }},
        }};
      }}

      return {{
        ...shared,
        theme: "base",
        darkMode: false,
        themeVariables: {{
          background: "#f8fafc",
          primaryColor: "#ffffff",
          primaryBorderColor: "#1f2937",
          primaryTextColor: "#111827",
          secondaryColor: "#f1f5f9",
          secondaryBorderColor: "#334155",
          secondaryTextColor: "#111827",
          tertiaryColor: "#e2e8f0",
          tertiaryBorderColor: "#334155",
          tertiaryTextColor: "#111827",
          lineColor: "#1f2937",
          textColor: "#111827",
          edgeLabelBackground: "#f8fafc",
          noteBkgColor: "#eef2ff",
          noteTextColor: "#111827",
          noteBorderColor: "#334155",
          actorBkg: "#ffffff",
          actorBorder: "#1f2937",
          actorTextColor: "#111827",
          actorLineColor: "#1f2937",
          signalColor: "#1f2937",
          clusterBkg: "#f1f5f9",
          clusterBorder: "#334155",
          labelTextColor: "#111827",
          cScale0: "#d1d5db",
          cScale1: "#e5e7eb",
          cScale2: "#f3f4f6",
          cScale3: "#e5e7eb",
          cScale4: "#d1d5db",
          cScale5: "#9ca3af",
          cScale6: "#6b7280",
          cScale7: "#4b5563",
          cScale8: "#334155",
          cScale9: "#1f2937",
        }},
      }};
    }};

    // Mermaid subtype matters for interaction and print layout because
    // sequence, ER, class, and flowchart diagrams have very different
    // geometry and typography tradeoffs.
    window.__mdexploreDetectMermaidKind = (sourceText) => {{
      const text = String(sourceText || "");
      if (/^\\s*sequenceDiagram\\b/im.test(text)) {{
        return "sequence";
      }}
      if (/^\\s*classDiagram\\b/im.test(text)) {{
        return "class";
      }}
      if (/^\\s*flowchart\\b/im.test(text) || /^\\s*graph\\b/im.test(text)) {{
        return "flowchart";
      }}
      if (/^\\s*erDiagram\\b/im.test(text)) {{
        return "er";
      }}
      return "";
    }};

    // Wrap Mermaid SVG output in an interactive shell that adds fit/zoom/pan
    // controls without mutating the underlying cached SVG markup.
    window.__mdexploreApplyMermaidZoomControls = (block, mode = "auto") => {{
      if (!(block instanceof HTMLElement)) {{
        return;
      }}
      const normalizedMode = String(mode || "").toLowerCase() === "pdf" ? "pdf" : "auto";
      const currentSvg = block.querySelector("svg");
      let currentShell = null;
      for (const child of Array.from(block.children || [])) {{
        if (child instanceof HTMLElement && child.classList.contains("mdexplore-mermaid-shell")) {{
          currentShell = child;
          break;
        }}
      }}
      const hashKey = String(block.getAttribute("data-mdexplore-mermaid-hash") || "").trim().toLowerCase();
      const mermaidIndex = String(block.getAttribute("data-mdexplore-mermaid-index") || "").trim();
      const stateKey = `mermaid:${{mermaidIndex || "0"}}:${{hashKey || "nohash"}}`;
      if (normalizedMode === "pdf") {{
        // Keep PDF output clean and unscaled.
        if (currentShell instanceof HTMLElement && currentSvg instanceof SVGElement) {{
          block.innerHTML = "";
          currentSvg.style.transform = "";
          currentSvg.style.width = "";
          currentSvg.style.maxWidth = "100%";
          block.appendChild(currentSvg);
        }}
        return;
      }}
      if (!(currentSvg instanceof SVGElement)) {{
        return;
      }}
      const currentParent = currentSvg.parentElement;
      if (
        currentShell instanceof HTMLElement &&
        currentParent instanceof HTMLElement &&
        currentParent.classList.contains("mdexplore-mermaid-viewport")
      ) {{
        const reapply = currentShell.__mdexploreReapplySavedState;
        if (typeof reapply === "function") {{
          try {{
            reapply();
          }} catch (_error) {{
            // Ignore stale wrapper reapply errors.
          }}
        }}
        return;
      }}

      // The shell operates in intrinsic SVG coordinates, so all geometry
      // helpers normalize whatever sizing hints the renderer emitted.
      const parseViewBox = (svgNode) => {{
        const viewBoxText = String(svgNode.getAttribute("viewBox") || "").trim();
        const parts = viewBoxText
          .split(/[\\s,]+/)
          .map((piece) => Number.parseFloat(piece))
          .filter((n) => Number.isFinite(n));
        if (parts.length === 4 && parts[2] > 1 && parts[3] > 1) {{
          return {{
            x: parts[0],
            y: parts[1],
            width: parts[2],
            height: parts[3],
          }};
        }}
        return null;
      }};

      // Some Mermaid outputs include generous whitespace in the original
      // viewBox. Tightening that once improves fit/zoom behavior and keeps the
      // initial "Fit" action visually sensible.
      const tightenSvgViewBoxWhitespace = (svgNode) => {{
        if (!(svgNode instanceof SVGElement)) {{
          return;
        }}
        if (svgNode.dataset && svgNode.dataset.mdexploreViewBoxTightened === "1") {{
          return;
        }}
        const parsedViewBox = parseViewBox(svgNode);
        if (!parsedViewBox) {{
          if (svgNode.dataset) {{
            svgNode.dataset.mdexploreViewBoxTightened = "1";
          }}
          return;
        }}
        let bbox = null;
        try {{
          bbox = svgNode.getBBox();
        }} catch (_error) {{
          bbox = null;
        }}
        if (!bbox || bbox.width <= 1 || bbox.height <= 1) {{
          if (svgNode.dataset) {{
            svgNode.dataset.mdexploreViewBoxTightened = "1";
          }}
          return;
        }}
        const widthGain = parsedViewBox.width / Math.max(1, bbox.width);
        const heightGain = parsedViewBox.height / Math.max(1, bbox.height);
        if (widthGain < 1.03 && heightGain < 1.03) {{
          if (svgNode.dataset) {{
            svgNode.dataset.mdexploreViewBoxTightened = "1";
          }}
          return;
        }}
        const padX = Math.max(6, bbox.width * 0.024);
        const padY = Math.max(6, bbox.height * 0.03);
        const minX = parsedViewBox.x;
        const minY = parsedViewBox.y;
        const maxX = parsedViewBox.x + parsedViewBox.width;
        const maxY = parsedViewBox.y + parsedViewBox.height;
        let newX = bbox.x - padX;
        let newY = bbox.y - padY;
        let newW = bbox.width + (padX * 2);
        let newH = bbox.height + (padY * 2);
        newX = Math.max(minX, newX);
        newY = Math.max(minY, newY);
        newW = Math.min(maxX - newX, newW);
        newH = Math.min(maxY - newY, newH);
        if (newW > 2 && newH > 2) {{
          svgNode.setAttribute("viewBox", `${{newX}} ${{newY}} ${{newW}} ${{newH}}`);
        }}
        if (svgNode.dataset) {{
          svgNode.dataset.mdexploreViewBoxTightened = "1";
        }}
      }};

      // Establish a stable intrinsic size before viewport math starts so zoom
      // state restore behaves consistently across revisits and rerenders.
      const parseBaseSize = (svgNode) => {{
        const parsedViewBox = parseViewBox(svgNode);
        if (parsedViewBox) {{
          return {{
            width: parsedViewBox.width,
            height: parsedViewBox.height,
          }};
        }}
        const widthAttr = Number.parseFloat(String(svgNode.getAttribute("width") || "").trim());
        const heightAttr = Number.parseFloat(String(svgNode.getAttribute("height") || "").trim());
        if (Number.isFinite(widthAttr) && widthAttr > 1 && Number.isFinite(heightAttr) && heightAttr > 1) {{
          return {{
            width: widthAttr,
            height: heightAttr,
          }};
        }}
        if (Number.isFinite(widthAttr) && widthAttr > 1) {{
          return {{
            width: widthAttr,
            height: Math.max(1, widthAttr * 0.62),
          }};
        }}
        try {{
          const bbox = svgNode.getBBox();
          if (bbox && bbox.width > 1 && bbox.height > 1) {{
            return {{
              width: bbox.width,
              height: bbox.height,
            }};
          }}
        }} catch (_error) {{
          // Ignore and fall back.
        }}
        const rect = svgNode.getBoundingClientRect();
        if (rect.width > 1 && rect.height > 1) {{
          return {{
            width: rect.width,
            height: rect.height,
          }};
        }}
        return {{
          width: 800,
          height: 520,
        }};
      }};

      // Toolbar + viewport form the reusable interactive shell around each
      // Mermaid block in GUI mode.
      const shell = document.createElement("div");
      shell.className = "mdexplore-mermaid-shell";
      shell.dataset.mdexploreStateKey = stateKey;
      const toolbar = document.createElement("div");
      toolbar.className = "mdexplore-mermaid-toolbar";
      const zoomOutBtn = document.createElement("button");
      zoomOutBtn.type = "button";
      zoomOutBtn.className = "mdexplore-mermaid-zoom-btn";
      zoomOutBtn.title = "Zoom out";
      zoomOutBtn.textContent = "−";
      const zoomInBtn = document.createElement("button");
      zoomInBtn.type = "button";
      zoomInBtn.className = "mdexplore-mermaid-zoom-btn";
      zoomInBtn.title = "Zoom in";
      zoomInBtn.textContent = "+";
      const zoomResetBtn = document.createElement("button");
      zoomResetBtn.type = "button";
      zoomResetBtn.className = "mdexplore-mermaid-zoom-btn";
      zoomResetBtn.title = "Fit diagram";
      zoomResetBtn.textContent = "Fit";
      const panLeftBtn = document.createElement("button");
      panLeftBtn.type = "button";
      panLeftBtn.className = "mdexplore-mermaid-zoom-btn";
      panLeftBtn.title = "Pan left";
      panLeftBtn.textContent = "←";
      const panUpBtn = document.createElement("button");
      panUpBtn.type = "button";
      panUpBtn.className = "mdexplore-mermaid-zoom-btn";
      panUpBtn.title = "Pan up";
      panUpBtn.textContent = "↑";
      const panDownBtn = document.createElement("button");
      panDownBtn.type = "button";
      panDownBtn.className = "mdexplore-mermaid-zoom-btn";
      panDownBtn.title = "Pan down";
      panDownBtn.textContent = "↓";
      const panRightBtn = document.createElement("button");
      panRightBtn.type = "button";
      panRightBtn.className = "mdexplore-mermaid-zoom-btn";
      panRightBtn.title = "Pan right";
      panRightBtn.textContent = "→";
      const zoomValue = document.createElement("span");
      zoomValue.className = "mdexplore-mermaid-zoom-value";
      zoomValue.textContent = "100%";
      toolbar.appendChild(zoomOutBtn);
      toolbar.appendChild(zoomInBtn);
      toolbar.appendChild(zoomResetBtn);
      toolbar.appendChild(panLeftBtn);
      toolbar.appendChild(panUpBtn);
      toolbar.appendChild(panDownBtn);
      toolbar.appendChild(panRightBtn);
      toolbar.appendChild(zoomValue);

      const viewport = document.createElement("div");
      viewport.className = "mdexplore-mermaid-viewport";
      viewport.tabIndex = 0;
      currentSvg.style.display = "block";
      currentSvg.style.transformOrigin = "top left";
      currentSvg.style.transformBox = "fill-box";
      currentSvg.style.maxWidth = "none";
      tightenSvgViewBoxWhitespace(currentSvg);

      const baseSize = parseBaseSize(currentSvg);
      currentSvg.style.width = `${{Math.max(32, Math.round(baseSize.width))}}px`;

      const clampZoom = (value) => Math.max(0.35, Math.min(4.0, value));
      let zoom = 1.0;
      let fitZoom = 1.0;
      let zoomDirty = false;
      let resizeObserver = null;
      let resizeDebounceTimer = null;
      let isPanning = false;
      let interactionArmed = false;
      let panStartClientX = 0;
      let panStartClientY = 0;
      let panStartScrollLeft = 0;
      let panStartScrollTop = 0;
      const MIN_VIEWPORT_HEIGHT = 220;
      const savedState = window.__mdexploreGetDiagramViewState(stateKey);
      if (savedState && typeof savedState === "object") {{
        zoomDirty = !!savedState.dirty;
      }}
      let saveState = () => {{}};

      const setViewportHeightForFit = (fitScale) => {{
        const scaledHeight = Math.max(80, baseSize.height * Math.max(0.1, fitScale));
        const idealHeight = Math.round(scaledHeight + 14);
        const maxHeight = Math.max(MIN_VIEWPORT_HEIGHT, Math.floor(window.innerHeight * 0.76));
        const finalHeight = Math.max(MIN_VIEWPORT_HEIGHT, Math.min(maxHeight, idealHeight));
        viewport.style.height = `${{finalHeight}}px`;
      }};

      const computeFitZoom = () => {{
        const widthPx = Math.max(1, baseSize.width);
        const viewportRectWidth = viewport.getBoundingClientRect().width;
        const blockRectWidth = block.getBoundingClientRect().width;
        const availableWidth = Math.max(
          120,
          Math.max(viewport.clientWidth, viewportRectWidth, blockRectWidth) - 12,
        );
        const fitByWidth = availableWidth / widthPx;
        // Width-first fit: initial/auto-fit should keep the full diagram width visible.
        fitZoom = clampZoom(Math.min(1.0, fitByWidth));
        return fitZoom;
      }};

      const applyZoom = (nextZoom, markDirty = false) => {{
        zoom = clampZoom(nextZoom);
        currentSvg.style.transform = `scale(${{zoom}})`;
        const pct = Math.round(zoom * 100);
        zoomValue.textContent = `${{pct}}%`;
        if (markDirty) {{
          zoomDirty = true;
        }}
        saveState();
      }};

      const applyFitIfClean = () => {{
        if (zoomDirty) {{
          return;
        }}
        const nextFit = computeFitZoom();
        setViewportHeightForFit(nextFit);
        applyZoom(nextFit, false);
      }};

      const panBy = (dx, dy) => {{
        viewport.scrollLeft += dx;
        viewport.scrollTop += dy;
        saveState();
      }};
      const setInteractionArmed = (nextArmed) => {{
        interactionArmed = !!nextArmed;
        viewport.classList.toggle("mdexplore-interaction-armed", interactionArmed);
        if (!interactionArmed) {{
          isPanning = false;
          viewport.classList.remove("mdexplore-pan-active");
        }}
      }};
      saveState = () => {{
        window.__mdexploreSetDiagramViewState(stateKey, {{
          zoom,
          scrollLeft: viewport.scrollLeft,
          scrollTop: viewport.scrollTop,
          dirty: zoomDirty,
        }});
      }};
      const applySavedState = (rawState) => {{
        if (!(rawState && typeof rawState === "object")) {{
          return false;
        }}
        const restoredZoom = Number(rawState.zoom);
        const restoredScrollLeft = Number(rawState.scrollLeft);
        const restoredScrollTop = Number(rawState.scrollTop);
        zoomDirty = !!rawState.dirty;
        const layoutFit = computeFitZoom();
        setViewportHeightForFit(layoutFit);
        applyZoom(Number.isFinite(restoredZoom) ? restoredZoom : layoutFit, false);
        const applyRestoredScroll = () => {{
          viewport.scrollLeft = Number.isFinite(restoredScrollLeft) ? restoredScrollLeft : 0;
          viewport.scrollTop = Number.isFinite(restoredScrollTop) ? restoredScrollTop : 0;
          saveState();
        }};
        applyRestoredScroll();
        window.requestAnimationFrame(() => {{
          applyRestoredScroll();
        }});
        window.setTimeout(() => {{
          applyRestoredScroll();
        }}, 70);
        saveState();
        return true;
      }};

      const scheduleFitIfClean = () => {{
        if (resizeDebounceTimer) {{
          window.clearTimeout(resizeDebounceTimer);
        }}
        resizeDebounceTimer = window.setTimeout(() => {{
          resizeDebounceTimer = null;
          applyFitIfClean();
        }}, 55);
      }};

      zoomOutBtn.addEventListener("click", () => {{
        setInteractionArmed(true);
        applyZoom(zoom / 1.2, true);
      }});
      zoomInBtn.addEventListener("click", () => {{
        setInteractionArmed(true);
        applyZoom(zoom * 1.2, true);
      }});
      zoomResetBtn.addEventListener("click", () => {{
        setInteractionArmed(true);
        zoomDirty = false;
        const nextFit = computeFitZoom();
        setViewportHeightForFit(nextFit);
        applyZoom(nextFit, false);
        viewport.scrollTop = 0;
        viewport.scrollLeft = 0;
        saveState();
      }});
      const PAN_STEP = 120;
      panLeftBtn.addEventListener("click", () => {{
        setInteractionArmed(true);
        panBy(-PAN_STEP, 0);
      }});
      panRightBtn.addEventListener("click", () => {{
        setInteractionArmed(true);
        panBy(PAN_STEP, 0);
      }});
      panUpBtn.addEventListener("click", () => {{
        setInteractionArmed(true);
        panBy(0, -PAN_STEP);
      }});
      panDownBtn.addEventListener("click", () => {{
        setInteractionArmed(true);
        panBy(0, PAN_STEP);
      }});
      viewport.addEventListener(
        "wheel",
        (event) => {{
          if (!interactionArmed) {{
            return;
          }}
          event.preventDefault();
          const direction = event.deltaY > 0 ? -1 : 1;
          applyZoom(direction > 0 ? zoom * 1.12 : zoom / 1.12, true);
        }},
        {{ passive: false }},
      );
      viewport.addEventListener("scroll", () => {{
        saveState();
      }}, {{ passive: true }});
      const onViewportKeyDown = (event) => {{
        if (!(event instanceof KeyboardEvent)) {{
          return;
        }}
        const key = String(event.key || "");
        if (!key.startsWith("Arrow")) {{
          return;
        }}
        event.preventDefault();
        const step = event.shiftKey ? PAN_STEP * 2 : PAN_STEP;
        if (key === "ArrowLeft") {{
          panBy(-step, 0);
        }} else if (key === "ArrowRight") {{
          panBy(step, 0);
        }} else if (key === "ArrowUp") {{
          panBy(0, -step);
        }} else if (key === "ArrowDown") {{
          panBy(0, step);
        }}
      }};
      viewport.addEventListener("keydown", onViewportKeyDown);

      const onPanStart = (event) => {{
        if (!(event instanceof MouseEvent) || event.button !== 0) {{
          return;
        }}
        if (!interactionArmed) {{
          return;
        }}
        if ((event.target instanceof Element) && event.target.closest(".mdexplore-mermaid-toolbar")) {{
          return;
        }}
        isPanning = true;
        panStartClientX = event.clientX;
        panStartClientY = event.clientY;
        panStartScrollLeft = viewport.scrollLeft;
        panStartScrollTop = viewport.scrollTop;
        viewport.classList.add("mdexplore-pan-active");
        event.preventDefault();
      }};
      const onViewportClick = (event) => {{
        if (!(event instanceof MouseEvent) || event.button !== 0) {{
          return;
        }}
        setInteractionArmed(!interactionArmed);
      }};
      const onPanMove = (event) => {{
        if (!isPanning || !(event instanceof MouseEvent)) {{
          return;
        }}
        const dx = event.clientX - panStartClientX;
        const dy = event.clientY - panStartClientY;
        viewport.scrollLeft = panStartScrollLeft - dx;
        viewport.scrollTop = panStartScrollTop - dy;
        saveState();
        event.preventDefault();
      }};
      const onPanEnd = () => {{
        if (!isPanning) {{
          return;
        }}
        isPanning = false;
        viewport.classList.remove("mdexplore-pan-active");
      }};
      const onViewportMouseLeave = () => {{
        setInteractionArmed(false);
      }};
      viewport.addEventListener("mousedown", onPanStart);
      viewport.addEventListener("click", onViewportClick);
      viewport.addEventListener("mouseleave", onViewportMouseLeave);
      window.addEventListener("mousemove", onPanMove);
      window.addEventListener("mouseup", onPanEnd);
      window.addEventListener("blur", onPanEnd);
      window.addEventListener("resize", scheduleFitIfClean);
      if (typeof ResizeObserver === "function") {{
        resizeObserver = new ResizeObserver(() => {{
          scheduleFitIfClean();
        }});
        resizeObserver.observe(viewport);
      }}

      viewport.appendChild(currentSvg);
      shell.appendChild(toolbar);
      shell.appendChild(viewport);
      block.innerHTML = "";
      block.appendChild(shell);
      setInteractionArmed(false);
      shell.__mdexploreReapplySavedState = () => {{
        const latest = window.__mdexploreGetDiagramViewState(stateKey);
        return applySavedState(latest);
      }};
      const applyInitialFitZoom = () => {{
        if (applySavedState(savedState)) {{
          return;
        }}
        zoomDirty = false;
        const nextFit = computeFitZoom();
        setViewportHeightForFit(nextFit);
        applyZoom(nextFit, false);
        viewport.scrollLeft = 0;
        viewport.scrollTop = 0;
        saveState();
      }};
      applyInitialFitZoom();
      shell.addEventListener("DOMNodeRemovedFromDocument", () => {{
        if (resizeDebounceTimer) {{
          window.clearTimeout(resizeDebounceTimer);
          resizeDebounceTimer = null;
        }}
        window.removeEventListener("resize", scheduleFitIfClean);
        viewport.removeEventListener("keydown", onViewportKeyDown);
        viewport.removeEventListener("mousedown", onPanStart);
        viewport.removeEventListener("click", onViewportClick);
        viewport.removeEventListener("mouseleave", onViewportMouseLeave);
        window.removeEventListener("mousemove", onPanMove);
        window.removeEventListener("mouseup", onPanEnd);
        window.removeEventListener("blur", onPanEnd);
        try {{
          delete shell.__mdexploreReapplySavedState;
        }} catch (_error) {{
          // Ignore cleanup errors.
        }}
        if (resizeObserver) {{
          try {{
            resizeObserver.disconnect();
          }} catch (_error) {{
            // Ignore cleanup errors.
          }}
          resizeObserver = null;
        }}
      }});
    }};

    window.__mdexploreApplyPlantUmlZoomControls = (mode = "auto") => {{
      const normalizedMode = String(mode || "").toLowerCase() === "pdf" ? "pdf" : "auto";
      const images = Array.from(document.querySelectorAll("img.plantuml"));
      let plantumlIndex = 0;
      for (const imgNode of images) {{
        if (!(imgNode instanceof HTMLImageElement)) {{
          continue;
        }}
        const fence = imgNode.closest(".mdexplore-fence");
        if (!(fence instanceof HTMLElement)) {{
          continue;
        }}
        const hashKey = String(fence.getAttribute("data-mdexplore-plantuml-hash") || "").trim().toLowerCase();
        const fenceId = String(fence.id || "").trim();
        const stateKey = `plantuml:${{fenceId || String(plantumlIndex)}}:${{hashKey || "nohash"}}`;
        plantumlIndex += 1;

        let currentShell = null;
        for (const child of Array.from(fence.children || [])) {{
          if (child instanceof HTMLElement && child.classList.contains("mdexplore-mermaid-shell")) {{
            currentShell = child;
            break;
          }}
        }}
        const currentImage = fence.querySelector("img.plantuml");
        if (!(currentImage instanceof HTMLImageElement)) {{
          continue;
        }}
        if (normalizedMode === "pdf") {{
          if (currentShell instanceof HTMLElement) {{
            fence.innerHTML = "";
            currentImage.style.transform = "";
            currentImage.style.width = "";
            currentImage.style.maxWidth = "100%";
            fence.appendChild(currentImage);
          }}
          continue;
        }}
        const currentParent = currentImage.parentElement;
        if (
          currentShell instanceof HTMLElement &&
          currentParent instanceof HTMLElement &&
          currentParent.classList.contains("mdexplore-mermaid-viewport")
        ) {{
          const reapply = currentShell.__mdexploreReapplySavedState;
          if (typeof reapply === "function") {{
            try {{
              reapply();
            }} catch (_error) {{
              // Ignore stale wrapper reapply errors.
            }}
          }}
          continue;
        }}

        let baseWidth = 800;
        let baseHeight = Math.max(1, baseWidth * 0.62);
        const updateBaseDimensions = () => {{
          let nextWidth = NaN;
          let nextHeight = NaN;
          if (Number.isFinite(currentImage.naturalWidth) && currentImage.naturalWidth > 1) {{
            nextWidth = currentImage.naturalWidth;
          }} else {{
            const widthAttr = Number.parseFloat(String(currentImage.getAttribute("width") || "").trim());
            if (Number.isFinite(widthAttr) && widthAttr > 1) {{
              nextWidth = widthAttr;
            }} else {{
              const rect = currentImage.getBoundingClientRect();
              if (rect.width > 1) {{
                nextWidth = rect.width;
              }}
            }}
          }}
          if (Number.isFinite(currentImage.naturalHeight) && currentImage.naturalHeight > 1) {{
            nextHeight = currentImage.naturalHeight;
          }} else {{
            const heightAttr = Number.parseFloat(String(currentImage.getAttribute("height") || "").trim());
            if (Number.isFinite(heightAttr) && heightAttr > 1) {{
              nextHeight = heightAttr;
            }} else {{
              const rect = currentImage.getBoundingClientRect();
              if (rect.height > 1) {{
                nextHeight = rect.height;
              }}
            }}
          }}
          if (Number.isFinite(nextWidth) && nextWidth > 1) {{
            baseWidth = nextWidth;
          }}
          if (Number.isFinite(nextHeight) && nextHeight > 1) {{
            baseHeight = nextHeight;
          }} else {{
            baseHeight = Math.max(1, baseWidth * 0.62);
          }}
        }};
        updateBaseDimensions();

        const shell = document.createElement("div");
        shell.className = "mdexplore-mermaid-shell";
        shell.dataset.mdexploreStateKey = stateKey;
        const toolbar = document.createElement("div");
        toolbar.className = "mdexplore-mermaid-toolbar";
        const zoomOutBtn = document.createElement("button");
        zoomOutBtn.type = "button";
        zoomOutBtn.className = "mdexplore-mermaid-zoom-btn";
        zoomOutBtn.title = "Zoom out";
        zoomOutBtn.textContent = "−";
        const zoomInBtn = document.createElement("button");
        zoomInBtn.type = "button";
        zoomInBtn.className = "mdexplore-mermaid-zoom-btn";
        zoomInBtn.title = "Zoom in";
        zoomInBtn.textContent = "+";
        const zoomResetBtn = document.createElement("button");
        zoomResetBtn.type = "button";
        zoomResetBtn.className = "mdexplore-mermaid-zoom-btn";
        zoomResetBtn.title = "Fit diagram";
        zoomResetBtn.textContent = "Fit";
        const panLeftBtn = document.createElement("button");
        panLeftBtn.type = "button";
        panLeftBtn.className = "mdexplore-mermaid-zoom-btn";
        panLeftBtn.title = "Pan left";
        panLeftBtn.textContent = "←";
        const panUpBtn = document.createElement("button");
        panUpBtn.type = "button";
        panUpBtn.className = "mdexplore-mermaid-zoom-btn";
        panUpBtn.title = "Pan up";
        panUpBtn.textContent = "↑";
        const panDownBtn = document.createElement("button");
        panDownBtn.type = "button";
        panDownBtn.className = "mdexplore-mermaid-zoom-btn";
        panDownBtn.title = "Pan down";
        panDownBtn.textContent = "↓";
        const panRightBtn = document.createElement("button");
        panRightBtn.type = "button";
        panRightBtn.className = "mdexplore-mermaid-zoom-btn";
        panRightBtn.title = "Pan right";
        panRightBtn.textContent = "→";
        const zoomValue = document.createElement("span");
        zoomValue.className = "mdexplore-mermaid-zoom-value";
        zoomValue.textContent = "100%";
        toolbar.appendChild(zoomOutBtn);
        toolbar.appendChild(zoomInBtn);
        toolbar.appendChild(zoomResetBtn);
        toolbar.appendChild(panLeftBtn);
        toolbar.appendChild(panUpBtn);
        toolbar.appendChild(panDownBtn);
        toolbar.appendChild(panRightBtn);
        toolbar.appendChild(zoomValue);

        const viewport = document.createElement("div");
        viewport.className = "mdexplore-mermaid-viewport";
        viewport.tabIndex = 0;
        currentImage.style.display = "block";
        currentImage.style.transformOrigin = "top left";
        currentImage.style.maxWidth = "none";
        currentImage.style.width = `${{Math.max(32, Math.round(baseWidth))}}px`;

        // PlantUML diagrams can be much wider than Mermaid diagrams; allow a
        // lower minimum zoom so width-fit can avoid right-edge clipping.
        const clampZoom = (value) => Math.max(0.1, Math.min(4.0, value));
        let zoom = 1.0;
        let fitZoom = 1.0;
        let zoomDirty = false;
        let resizeObserver = null;
        let resizeDebounceTimer = null;
        let postLayoutFitTimers = [];
        let isPanning = false;
        let interactionArmed = false;
        let panStartClientX = 0;
        let panStartClientY = 0;
        let panStartScrollLeft = 0;
        let panStartScrollTop = 0;
        const MIN_VIEWPORT_HEIGHT = 96;
        const savedState = window.__mdexploreGetDiagramViewState(stateKey);
        if (savedState && typeof savedState === "object") {{
          zoomDirty = !!savedState.dirty;
        }}
        let saveState = () => {{}};

        const setViewportHeightForFit = (fitScale) => {{
          const scaledHeight = Math.max(24, baseHeight * Math.max(0.1, fitScale));
          // Match viewport height to width-fit diagram height with only light breathing room.
          const verticalPadding = Math.max(6, Math.round(scaledHeight * 0.05));
          const finalHeight = Math.max(MIN_VIEWPORT_HEIGHT, Math.round(scaledHeight + verticalPadding));
          viewport.style.height = `${{finalHeight}}px`;
        }};

        const getViewportInnerWidth = () => {{
          const viewportStyles = window.getComputedStyle(viewport);
          const padLeft = Number.parseFloat(String(viewportStyles.paddingLeft || "0")) || 0;
          const padRight = Number.parseFloat(String(viewportStyles.paddingRight || "0")) || 0;
          return Math.max(80, viewport.clientWidth - padLeft - padRight - 2);
        }};
        const getViewportInnerBounds = () => {{
          const viewportStyles = window.getComputedStyle(viewport);
          const padLeft = Number.parseFloat(String(viewportStyles.paddingLeft || "0")) || 0;
          const padRight = Number.parseFloat(String(viewportStyles.paddingRight || "0")) || 0;
          const rect = viewport.getBoundingClientRect();
          const innerLeft = rect.left + padLeft;
          const innerWidth = Math.max(80, viewport.clientWidth - padLeft - padRight - 2);
          return {{
            innerLeft,
            innerRight: innerLeft + innerWidth,
            innerWidth,
          }};
        }};

        const computeFitZoom = () => {{
          const innerWidth = getViewportInnerWidth();
          // Keep an explicit safety margin; very wide PlantUML diagrams can clip
          // by a few pixels on first layout due to transform rounding.
          const fitByWidth = (innerWidth / Math.max(1, baseWidth)) * 0.97;
          fitZoom = clampZoom(Math.min(1.0, fitByWidth));
          return fitZoom;
        }};

        const applyZoom = (nextZoom, markDirty = false) => {{
          zoom = clampZoom(nextZoom);
          currentImage.style.transform = `scale(${{zoom}})`;
          const pct = Math.round(zoom * 100);
          zoomValue.textContent = `${{pct}}%`;
          if (markDirty) {{
            zoomDirty = true;
          }}
          saveState();
        }};

        const panBy = (dx, dy) => {{
          viewport.scrollLeft += dx;
          viewport.scrollTop += dy;
          saveState();
        }};
        const setInteractionArmed = (nextArmed) => {{
          interactionArmed = !!nextArmed;
          viewport.classList.toggle("mdexplore-interaction-armed", interactionArmed);
          if (!interactionArmed) {{
            isPanning = false;
            viewport.classList.remove("mdexplore-pan-active");
          }}
        }};
        saveState = () => {{
          window.__mdexploreSetDiagramViewState(stateKey, {{
            zoom,
            scrollLeft: viewport.scrollLeft,
            scrollTop: viewport.scrollTop,
            dirty: zoomDirty,
          }});
        }};
        const applySavedState = (rawState) => {{
          if (!(rawState && typeof rawState === "object")) {{
            return false;
          }}
          const restoredZoom = Number(rawState.zoom);
          const restoredScrollLeft = Number(rawState.scrollLeft);
          const restoredScrollTop = Number(rawState.scrollTop);
          zoomDirty = !!rawState.dirty;
          const layoutFit = computeFitZoom();
          let targetZoom = layoutFit;
          let zoomWasClampedForFit = false;
          if (Number.isFinite(restoredZoom) && restoredZoom > 0) {{
            targetZoom = clampZoom(restoredZoom);
            if (targetZoom > layoutFit) {{
              // Never restore into a clipped initial view.
              targetZoom = layoutFit;
              zoomWasClampedForFit = true;
            }}
          }}
          setViewportHeightForFit(targetZoom);
          applyZoom(targetZoom, false);
          if (!zoomDirty) {{
            // Ensure exact visual fit after layout/pixel rounding.
            applyCleanFitZoom();
            zoomWasClampedForFit = false;
          }}
          const applyRestoredScroll = () => {{
            viewport.scrollLeft = zoomWasClampedForFit ? 0 : (Number.isFinite(restoredScrollLeft) ? restoredScrollLeft : 0);
            viewport.scrollTop = zoomWasClampedForFit ? 0 : (Number.isFinite(restoredScrollTop) ? restoredScrollTop : 0);
            saveState();
          }};
          applyRestoredScroll();
          window.requestAnimationFrame(() => {{
            applyRestoredScroll();
          }});
          window.setTimeout(() => {{
            applyRestoredScroll();
          }}, 70);
          saveState();
          return true;
        }};
        const applyFitIfClean = () => {{
          if (zoomDirty) {{
            return;
          }}
          applyCleanFitZoom();
        }};
        const remeasureAndRefit = (forceReapply = false) => {{
          const previousWidth = baseWidth;
          const previousHeight = baseHeight;
          updateBaseDimensions();
          if (!forceReapply && Math.abs(baseWidth - previousWidth) < 0.5 && Math.abs(baseHeight - previousHeight) < 0.5) {{
            return;
          }}
          currentImage.style.width = `${{Math.max(32, Math.round(baseWidth))}}px`;
          const nextFit = computeFitZoom();
          setViewportHeightForFit(nextFit);
          if (!zoomDirty) {{
            applyCleanFitZoom();
          }} else {{
            applyZoom(zoom, false);
          }}
          saveState();
        }};
        const measureHorizontalOverflow = () => {{
          const bounds = getViewportInnerBounds();
          const imageRect = currentImage.getBoundingClientRect();
          // Positive means image is extending past the viewport's right edge.
          const rightOverflow = imageRect.right - bounds.innerRight;
          // Positive means image started before the viewport's left edge.
          const leftOverflow = bounds.innerLeft - imageRect.left;
          return {{
            rightOverflow: Number.isFinite(rightOverflow) ? rightOverflow : 0,
            leftOverflow: Number.isFinite(leftOverflow) ? leftOverflow : 0,
            imageWidth: Math.max(1, imageRect.width),
            innerWidth: Math.max(1, bounds.innerWidth),
          }};
        }};
        const applyCleanFitZoom = () => {{
          let candidate = computeFitZoom();
          setViewportHeightForFit(candidate);
          applyZoom(candidate, false);
          // Refine fit from actual post-transform geometry. This is more
          // reliable than scrollWidth for transformed PlantUML images.
          for (let pass = 0; pass < 7; pass += 1) {{
            const metrics = measureHorizontalOverflow();
            const needsRightFix = metrics.rightOverflow > 0.35;
            const needsLeftFix = metrics.leftOverflow > 0.35;
            if (!needsRightFix && !needsLeftFix) {{
              break;
            }}
            const targetWidth = Math.max(1, metrics.innerWidth - 2);
            const widthRatio = targetWidth / metrics.imageWidth;
            const correction = Math.max(0.65, Math.min(0.995, widthRatio));
            candidate = clampZoom(candidate * correction);
            setViewportHeightForFit(candidate);
            applyZoom(candidate, false);
            // Re-anchor at origin while fitting so width checks are stable.
            viewport.scrollLeft = 0;
          }}
          viewport.scrollLeft = 0;
        }};
        const clearPostLayoutFitTimers = () => {{
          for (const timerId of postLayoutFitTimers) {{
            try {{
              window.clearTimeout(timerId);
            }} catch (_error) {{
              // Ignore timer cleanup errors.
            }}
          }}
          postLayoutFitTimers = [];
        }};
        const schedulePostLayoutFitPasses = () => {{
          clearPostLayoutFitTimers();
          const runFitPass = () => {{
            if (zoomDirty) {{
              return;
            }}
            applyCleanFitZoom();
            viewport.scrollLeft = 0;
          }};
          // Refit across a few late layout phases to avoid first-open clipping.
          const immediate = window.setTimeout(() => {{
            window.requestAnimationFrame(() => {{
              window.requestAnimationFrame(() => {{
                runFitPass();
              }});
            }});
          }}, 0);
          postLayoutFitTimers.push(immediate);
          for (const delayMs of [50, 140, 320]) {{
            const timerId = window.setTimeout(() => {{
              runFitPass();
            }}, delayMs);
            postLayoutFitTimers.push(timerId);
          }}
        }};
        const scheduleFitIfClean = () => {{
          if (resizeDebounceTimer) {{
            window.clearTimeout(resizeDebounceTimer);
          }}
          resizeDebounceTimer = window.setTimeout(() => {{
            resizeDebounceTimer = null;
            applyFitIfClean();
            schedulePostLayoutFitPasses();
          }}, 55);
        }};

        zoomOutBtn.addEventListener("click", () => {{
          setInteractionArmed(true);
          applyZoom(zoom / 1.2, true);
        }});
        zoomInBtn.addEventListener("click", () => {{
          setInteractionArmed(true);
          applyZoom(zoom * 1.2, true);
        }});
        zoomResetBtn.addEventListener("click", () => {{
          setInteractionArmed(true);
          zoomDirty = false;
          applyCleanFitZoom();
          viewport.scrollTop = 0;
          viewport.scrollLeft = 0;
          saveState();
        }});
        const PAN_STEP = 120;
        panLeftBtn.addEventListener("click", () => {{
          setInteractionArmed(true);
          panBy(-PAN_STEP, 0);
        }});
        panRightBtn.addEventListener("click", () => {{
          setInteractionArmed(true);
          panBy(PAN_STEP, 0);
        }});
        panUpBtn.addEventListener("click", () => {{
          setInteractionArmed(true);
          panBy(0, -PAN_STEP);
        }});
        panDownBtn.addEventListener("click", () => {{
          setInteractionArmed(true);
          panBy(0, PAN_STEP);
        }});
        viewport.addEventListener(
          "wheel",
          (event) => {{
            if (!interactionArmed) {{
              return;
            }}
            event.preventDefault();
            const direction = event.deltaY > 0 ? -1 : 1;
            applyZoom(direction > 0 ? zoom * 1.12 : zoom / 1.12, true);
          }},
          {{ passive: false }},
        );
        viewport.addEventListener("scroll", () => {{
          saveState();
        }}, {{ passive: true }});
        const onViewportKeyDown = (event) => {{
          if (!(event instanceof KeyboardEvent)) {{
            return;
          }}
          const key = String(event.key || "");
          if (!key.startsWith("Arrow")) {{
            return;
          }}
          event.preventDefault();
          const step = event.shiftKey ? PAN_STEP * 2 : PAN_STEP;
          if (key === "ArrowLeft") {{
            panBy(-step, 0);
          }} else if (key === "ArrowRight") {{
            panBy(step, 0);
          }} else if (key === "ArrowUp") {{
            panBy(0, -step);
          }} else if (key === "ArrowDown") {{
            panBy(0, step);
          }}
        }};
        viewport.addEventListener("keydown", onViewportKeyDown);
        const onPanStart = (event) => {{
          if (!(event instanceof MouseEvent) || event.button !== 0) {{
            return;
          }}
          if (!interactionArmed) {{
            return;
          }}
          if ((event.target instanceof Element) && event.target.closest(".mdexplore-mermaid-toolbar")) {{
            return;
          }}
          isPanning = true;
          panStartClientX = event.clientX;
          panStartClientY = event.clientY;
          panStartScrollLeft = viewport.scrollLeft;
          panStartScrollTop = viewport.scrollTop;
          viewport.classList.add("mdexplore-pan-active");
          event.preventDefault();
        }};
        const onViewportClick = (event) => {{
          if (!(event instanceof MouseEvent) || event.button !== 0) {{
            return;
          }}
          setInteractionArmed(!interactionArmed);
        }};
        const onPanMove = (event) => {{
          if (!isPanning || !(event instanceof MouseEvent)) {{
            return;
          }}
          const dx = event.clientX - panStartClientX;
          const dy = event.clientY - panStartClientY;
          viewport.scrollLeft = panStartScrollLeft - dx;
          viewport.scrollTop = panStartScrollTop - dy;
          saveState();
          event.preventDefault();
        }};
        const onPanEnd = () => {{
          if (!isPanning) {{
            return;
          }}
          isPanning = false;
          viewport.classList.remove("mdexplore-pan-active");
        }};
        const onViewportMouseLeave = () => {{
          setInteractionArmed(false);
        }};
        viewport.addEventListener("mousedown", onPanStart);
        viewport.addEventListener("click", onViewportClick);
        viewport.addEventListener("mouseleave", onViewportMouseLeave);
        window.addEventListener("mousemove", onPanMove);
        window.addEventListener("mouseup", onPanEnd);
        window.addEventListener("blur", onPanEnd);
        window.addEventListener("resize", scheduleFitIfClean);
        if (typeof ResizeObserver === "function") {{
          resizeObserver = new ResizeObserver(() => {{
            scheduleFitIfClean();
          }});
          resizeObserver.observe(viewport);
        }}

        viewport.appendChild(currentImage);
        shell.appendChild(toolbar);
        shell.appendChild(viewport);
        fence.innerHTML = "";
        fence.appendChild(shell);
        const handleImageReady = () => {{
          remeasureAndRefit(true);
          schedulePostLayoutFitPasses();
        }};
        if (!currentImage.complete || !(Number.isFinite(currentImage.naturalWidth) && currentImage.naturalWidth > 1)) {{
          currentImage.addEventListener("load", handleImageReady, {{ once: true }});
          if (typeof currentImage.decode === "function") {{
            currentImage
              .decode()
              .then(() => handleImageReady())
              .catch(() => {{
                // Ignore decode errors; load event path handles fallback.
              }});
          }}
        }} else {{
          window.requestAnimationFrame(() => handleImageReady());
        }}
        setInteractionArmed(false);
        shell.__mdexploreReapplySavedState = () => {{
          const latest = window.__mdexploreGetDiagramViewState(stateKey);
          return applySavedState(latest);
        }};
        const applyInitialFitZoom = () => {{
          if (applySavedState(savedState)) {{
            schedulePostLayoutFitPasses();
            return;
          }}
          zoomDirty = false;
          applyCleanFitZoom();
          viewport.scrollLeft = 0;
          viewport.scrollTop = 0;
          saveState();
          schedulePostLayoutFitPasses();
        }};
        applyInitialFitZoom();
        shell.addEventListener("DOMNodeRemovedFromDocument", () => {{
          if (resizeDebounceTimer) {{
            window.clearTimeout(resizeDebounceTimer);
            resizeDebounceTimer = null;
          }}
          clearPostLayoutFitTimers();
          window.removeEventListener("resize", scheduleFitIfClean);
          viewport.removeEventListener("keydown", onViewportKeyDown);
          viewport.removeEventListener("mousedown", onPanStart);
          viewport.removeEventListener("click", onViewportClick);
          viewport.removeEventListener("mouseleave", onViewportMouseLeave);
          window.removeEventListener("mousemove", onPanMove);
          window.removeEventListener("mouseup", onPanEnd);
          window.removeEventListener("blur", onPanEnd);
          try {{
            delete shell.__mdexploreReapplySavedState;
          }} catch (_error) {{
            // Ignore cleanup errors.
          }}
          if (resizeObserver) {{
            try {{
              resizeObserver.disconnect();
            }} catch (_error) {{
              // Ignore cleanup errors.
            }}
            resizeObserver = null;
          }}
        }});
      }}
    }};

    window.__mdexploreApplyMermaidPostStyles = (block, mode = "auto") => {{
      if (!(block instanceof HTMLElement)) {{
        return;
      }}
      const normalizedMode = String(mode || "").toLowerCase() === "pdf" ? "pdf" : "auto";
      if (document.body && document.body.classList.contains("mdexplore-pdf-export-mode")) {{
        // Defensive recovery: stale PDF mode should never suppress normal
        // Mermaid controls in interactive preview mode.
        if (normalizedMode !== "pdf" && window.__mdexploreClearPdfExportMode) {{
          window.__mdexploreClearPdfExportMode();
        }}
        window.__mdexploreApplyMermaidZoomControls(block, "pdf");
        if (normalizedMode !== "pdf") {{
          window.__mdexploreApplyMermaidZoomControls(block, normalizedMode);
        }}
        return;
      }}
      window.__mdexploreApplyMermaidZoomControls(block, normalizedMode);
      if (normalizedMode === "pdf") {{
        return;
      }}
      if (!window.__mdexploreIsDarkBackground()) {{
        return;
      }}

      const svg = block.querySelector("svg");
      if (!(svg instanceof SVGElement)) {{
        return;
      }}

      const hardenGenericEdgesAndLabels = () => {{
        const edgeStrokeColor = "#eaf2ff";
        const boundaryStrokeColor = "#c3d4ef";
        const edgeLabelColor = "#ffffff";
        const edgeLabelBackground = "#1e293b";

        const edgeSelectors = [
          ".edge-thickness-normal",
          ".edge-thickness-thick",
          ".edge-pattern-solid",
          ".edge-pattern-dashed",
          ".edge-pattern-dotted",
          ".flowchart-link",
          ".relationshipLine",
          ".messageLine0",
          ".messageLine1",
          ".loopLine",
          ".activation0",
          ".activation1",
        ];
        for (const selector of edgeSelectors) {{
          const nodes = svg.querySelectorAll(selector);
          for (const edgeNode of nodes) {{
            if (!(edgeNode instanceof SVGElement)) {{
              continue;
            }}
            edgeNode.setAttribute("stroke", edgeStrokeColor);
            edgeNode.style.stroke = edgeStrokeColor;
            edgeNode.style.strokeOpacity = "1";
            edgeNode.style.opacity = "1";
          }}
        }}

        const styleBlackSelectors = [
          'path[style*="stroke:#000"]',
          'path[style*="stroke: #000"]',
          'path[style*="stroke:black"]',
          'path[style*="stroke: black"]',
          'line[style*="stroke:#000"]',
          'line[style*="stroke: #000"]',
          'line[style*="stroke:black"]',
          'line[style*="stroke: black"]',
        ];
        for (const selector of styleBlackSelectors) {{
          const nodes = svg.querySelectorAll(selector);
          for (const edgeNode of nodes) {{
            if (!(edgeNode instanceof SVGElement)) {{
              continue;
            }}
            edgeNode.setAttribute("stroke", edgeStrokeColor);
            edgeNode.style.stroke = edgeStrokeColor;
            edgeNode.style.strokeOpacity = "1";
            edgeNode.style.opacity = "1";
          }}
        }}

        // Fallback for diagrams (notably C4) that emit plain, unclassed edge
        // geometry with inline stroke/fill:none and marker endpoints.
        const geometricEdgeNodes = svg.querySelectorAll("path, line, polyline");
        for (const edgeNode of geometricEdgeNodes) {{
          if (!(edgeNode instanceof SVGElement)) {{
            continue;
          }}
          if (edgeNode.closest("defs, marker, symbol")) {{
            continue;
          }}
          const styleText = String(edgeNode.getAttribute("style") || "").toLowerCase();
          const fillAttr = String(edgeNode.getAttribute("fill") || "").trim().toLowerCase();
          const strokeAttr = String(edgeNode.getAttribute("stroke") || "").trim().toLowerCase();
          const hasMarker =
            edgeNode.hasAttribute("marker-end") ||
            edgeNode.hasAttribute("marker-start") ||
            styleText.includes("marker-end") ||
            styleText.includes("marker-start");
          const fillIsNone =
            fillAttr == "none" ||
            styleText.includes("fill:none") ||
            styleText.includes("fill: none");
          const hasStrokeHint =
            strokeAttr.length > 0 ||
            styleText.includes("stroke:") ||
            styleText.includes("stroke=");
          if (!(hasMarker || (fillIsNone && hasStrokeHint))) {{
            continue;
          }}
          edgeNode.setAttribute("stroke", edgeStrokeColor);
          edgeNode.style.stroke = edgeStrokeColor;
          edgeNode.style.strokeOpacity = "1";
          edgeNode.style.opacity = "1";
        }}

        const markerNodes = svg.querySelectorAll(".marker, .marker path, marker path");
        for (const markerNode of markerNodes) {{
          if (!(markerNode instanceof SVGElement)) {{
            continue;
          }}
          markerNode.setAttribute("stroke", edgeStrokeColor);
          markerNode.style.stroke = edgeStrokeColor;
          markerNode.setAttribute("fill", edgeStrokeColor);
          markerNode.style.fill = edgeStrokeColor;
          markerNode.style.strokeOpacity = "1";
          markerNode.style.fillOpacity = "1";
          markerNode.style.opacity = "1";
        }}

        const boundarySelectors = [
          "rect[stroke-dasharray]",
          'rect[style*="stroke-dasharray"]',
        ];
        for (const selector of boundarySelectors) {{
          const nodes = svg.querySelectorAll(selector);
          for (const boundaryNode of nodes) {{
            if (!(boundaryNode instanceof SVGElement)) {{
              continue;
            }}
            const dashText = String(
              boundaryNode.getAttribute("stroke-dasharray") || boundaryNode.style.strokeDasharray || ""
            ).trim();
            if (!dashText) {{
              continue;
            }}
            const dashParts = dashText
              .split(/[\\s,]+/)
              .map((part) => Number.parseFloat(part))
              .filter((value) => Number.isFinite(value));
            if (!dashParts.some((value) => value > 0.01)) {{
              continue;
            }}
            const fillAttr = String(boundaryNode.getAttribute("fill") || "").trim().toLowerCase();
            const styleFill = String(boundaryNode.style.fill || "").trim().toLowerCase();
            const fillLooksNone =
              fillAttr === "none" ||
              fillAttr === "transparent" ||
              styleFill === "none" ||
              styleFill === "transparent" ||
              styleFill === "";
            if (!fillLooksNone) {{
              continue;
            }}
            boundaryNode.setAttribute("stroke", boundaryStrokeColor);
            boundaryNode.style.stroke = boundaryStrokeColor;
            boundaryNode.style.strokeOpacity = "0.96";
          }}
        }}

        const labelBgNodes = svg.querySelectorAll(
          ".labelBkg, .edgeLabel rect, rect.edgeLabel, rect.sequenceEdgeLabel, rect[class*='edgeLabel']"
        );
        for (const bgNode of labelBgNodes) {{
          if (!(bgNode instanceof SVGElement)) {{
            continue;
          }}
          bgNode.setAttribute("fill", edgeLabelBackground);
          bgNode.style.fill = edgeLabelBackground;
          bgNode.setAttribute("stroke", "#93c5fd");
          bgNode.style.stroke = "#93c5fd";
        }}

        const labelSelectors = [
          "g.edgeLabel",
          "g.edgeLabel *",
          ".messageText",
          ".messageText *",
          ".relation",
          ".relation *",
          "[class*='edgeLabel'] text",
          "[class*='edgeLabel'] tspan",
        ];
        for (const selector of labelSelectors) {{
          const nodes = svg.querySelectorAll(selector);
          for (const labelNode of nodes) {{
            if (labelNode instanceof HTMLElement) {{
              labelNode.style.color = edgeLabelColor;
              labelNode.style.fill = edgeLabelColor;
              labelNode.style.opacity = "1";
              continue;
            }}
            if (labelNode instanceof SVGElement) {{
              labelNode.setAttribute("fill", edgeLabelColor);
              labelNode.style.fill = edgeLabelColor;
              labelNode.style.opacity = "1";
            }}
          }}
        }}
      }};

      const parseAnyColorRgb = (rawColor) => {{
        const raw = String(rawColor || "").trim();
        if (!raw || raw === "none" || raw === "transparent" || raw === "currentColor") {{
          return null;
        }}
        const rgbMatch = raw.match(/^rgba?\\(([^)]+)\\)$/i);
        if (rgbMatch) {{
          const rawParts = rgbMatch[1].split(",").map((part) => part.trim());
          const parts = rawParts
            .map((part) => Number.parseFloat(part))
            .filter((value) => Number.isFinite(value));
          if (parts.length >= 4 && parts[3] <= 0.01) {{
            return null;
          }}
          if (parts.length >= 3) {{
            return [parts[0], parts[1], parts[2]];
          }}
        }}
        const hexMatch = raw.match(/^#([0-9a-f]{3}|[0-9a-f]{6})$/i);
        if (hexMatch) {{
          const value = hexMatch[1];
          if (value.length === 3) {{
            return [
              Number.parseInt(value[0] + value[0], 16),
              Number.parseInt(value[1] + value[1], 16),
              Number.parseInt(value[2] + value[2], 16),
            ];
          }}
          return [
            Number.parseInt(value.slice(0, 2), 16),
            Number.parseInt(value.slice(2, 4), 16),
            Number.parseInt(value.slice(4, 6), 16),
          ];
        }}
        return null;
      }};

      const relativeLuminance = (rgb) => {{
        if (!Array.isArray(rgb) || rgb.length < 3) {{
          return 0;
        }}
        const toLinear = (value) => {{
          const v = Math.max(0, Math.min(255, Number(value) || 0)) / 255;
          return v <= 0.03928 ? (v / 12.92) : Math.pow((v + 0.055) / 1.055, 2.4);
        }};
        const r = toLinear(rgb[0]);
        const g = toLinear(rgb[1]);
        const b = toLinear(rgb[2]);
        return (0.2126 * r) + (0.7152 * g) + (0.0722 * b);
      }};

      const contrastRatio = (fg, bg) => {{
        const l1 = relativeLuminance(fg);
        const l2 = relativeLuminance(bg);
        const bright = Math.max(l1, l2);
        const dark = Math.min(l1, l2);
        return (bright + 0.05) / (dark + 0.05);
      }};

      const clampColor = (value) => Math.max(0, Math.min(255, Math.round(value)));
      const rgbToCss = (rgb) => `rgb(${{clampColor(rgb[0])}}, ${{clampColor(rgb[1])}}, ${{clampColor(rgb[2])}})`;
      const darkenRgb = (rgb, factor) => {{
        const f = Math.max(0, Math.min(0.6, Number(factor) || 0));
        return [
          clampColor(rgb[0] * (1.0 - f)),
          clampColor(rgb[1] * (1.0 - f)),
          clampColor(rgb[2] * (1.0 - f)),
        ];
      }};

      const hardenNodeAndLabelContrast = () => {{
        const LIGHT_TEXT = "#f8fbff";
        const DARK_TEXT = "#0f172a";
        const LIGHT_TEXT_RGB = [248, 251, 255];
        const DARK_TEXT_RGB = [15, 23, 42];
        const EDGE_TEXT = "#ffffff";
        const pageBgRgb = (() => {{
          let node = block;
          while (node instanceof HTMLElement) {{
            const bg = getComputedStyle(node).backgroundColor || "";
            const rgb = parseAnyColorRgb(bg);
            if (rgb) {{
              return rgb;
            }}
            node = node.parentElement;
          }}
          const fallbackBg = getComputedStyle(document.body || document.documentElement).backgroundColor || "";
          return parseAnyColorRgb(fallbackBg) || [15, 23, 42];
        }})();
        const svgArea = (() => {{
          try {{
            const b = svg.getBBox();
            if (b && b.width > 0.5 && b.height > 0.5) {{
              return b.width * b.height;
            }}
          }} catch (_error) {{
            // Ignore and use fallback area.
          }}
          return 1;
        }})();
        const parseNumber = (raw, fallback = Number.NaN) => {{
          const n = Number.parseFloat(String(raw ?? "").trim());
          return Number.isFinite(n) ? n : fallback;
        }};

        const shapeSamples = [];
        const shapeNodes = svg.querySelectorAll("rect, path, polygon, ellipse, circle");
        for (const shapeNode of shapeNodes) {{
          if (!(shapeNode instanceof SVGGraphicsElement)) {{
            continue;
          }}
          if (shapeNode.closest("defs, marker, symbol")) {{
            continue;
          }}
          const classText = String(shapeNode.getAttribute("class") || "").toLowerCase();
          if (
            classText.includes("relationshipline") ||
              classText.includes("edge") ||
              classText.includes("marker") ||
              classText.includes("edgelabel") ||
              classText.includes("labelbkg") ||
              classText.includes("relationlabel") ||
              classText.includes("messagetext")
            ) {{
              continue;
            }}
          const computed = getComputedStyle(shapeNode);
          const styleText = String(shapeNode.getAttribute("style") || "").toLowerCase();
          if (
            styleText.includes("display:none") ||
            styleText.includes("display: none") ||
            computed.display === "none" ||
            computed.visibility === "hidden"
          ) {{
            continue;
          }}
          if (styleText.includes("fill:none") || styleText.includes("fill: none")) {{
            continue;
          }}
          const fillOpacity = parseNumber(
            shapeNode.getAttribute("fill-opacity"),
            parseNumber(shapeNode.style.fillOpacity, parseNumber(computed.fillOpacity, 1))
          );
          const nodeOpacity = parseNumber(
            shapeNode.getAttribute("opacity"),
            parseNumber(shapeNode.style.opacity, parseNumber(computed.opacity, 1))
          );
          if (fillOpacity <= 0.05 || nodeOpacity <= 0.05) {{
            continue;
          }}
          const fillText = String(
            shapeNode.getAttribute("fill") || shapeNode.style.fill || computed.fill || ""
          ).trim();
          const rgb = parseAnyColorRgb(fillText);
          if (!rgb) {{
            continue;
          }}
          let bbox = null;
          try {{
            bbox = shapeNode.getBBox();
          }} catch (_error) {{
            bbox = null;
          }}
          if (!bbox || bbox.width <= 1 || bbox.height <= 1) {{
            continue;
          }}
          const area = bbox.width * bbox.height;
          shapeSamples.push({{
            node: shapeNode,
            x1: bbox.x,
            y1: bbox.y,
            x2: bbox.x + bbox.width,
            y2: bbox.y + bbox.height,
            area,
            rgb,
          }});
        }}

        if (shapeSamples.length === 0) {{
          return;
        }}

        // Slightly darken medium-light blue fills in dark mode so white node
        // labels are easier to read.
        for (const sample of shapeSamples) {{
          const [r, g, b] = sample.rgb;
          const lum = relativeLuminance(sample.rgb);
          const max = Math.max(r, g, b);
          const min = Math.min(r, g, b);
          const saturation = max <= 0 ? 0 : (max - min) / max;
          const blueDominant = b >= g + 10 && b >= r + 10;
          const shouldDarken = blueDominant && saturation >= 0.08 && lum >= 0.42 && lum <= 0.78;
          if (!shouldDarken) {{
            continue;
          }}
          const darkened = darkenRgb(sample.rgb, 0.27);
          const cssColor = rgbToCss(darkened);
          sample.node.setAttribute("fill", cssColor);
          sample.node.style.fill = cssColor;
          sample.rgb = darkened;
        }}

        const sampleAtPoint = (x, y) => {{
          let best = null;
          let bestArea = Number.POSITIVE_INFINITY;
          for (const sample of shapeSamples) {{
            if (x < sample.x1 || x > sample.x2 || y < sample.y1 || y > sample.y2) {{
              continue;
            }}
            if (sample.area < bestArea) {{
              bestArea = sample.area;
              best = sample;
            }}
          }}
          return best && bestArea < svgArea * 0.45 ? best : null;
        }};

        const preferredTextColor = (bgRgb) => {{
          const lightScore = contrastRatio(LIGHT_TEXT_RGB, bgRgb);
          const darkScore = contrastRatio(DARK_TEXT_RGB, bgRgb);
          return lightScore >= darkScore ? LIGHT_TEXT : DARK_TEXT;
        }};

        const isLikelyNodeText = (node) => {{
          if (!(node instanceof Element)) {{
            return false;
          }}
          return !!node.closest(
            "g.node, g[class*='node'], g[class*='actor'], g[class*='entity'], g[class*='cluster'], g[class*='row-rect'], .nodeLabel, .entityLabel, .er.entityBox"
          );
        }};

        const isEdgeLikeText = (node, localSample, fontSizePx, textValue = "") => {{
          if (!(node instanceof Element)) {{
            return false;
          }}
          if (node.closest(".edgeLabel, .messageText, .relation, .label")) {{
            return true;
          }}
          const classText = String(node.getAttribute("class") || "").toLowerCase();
          const hasClassHint = (
            classText.includes("edge") ||
            classText.includes("relation") ||
            classText.includes("message") ||
            classText.includes("label")
          );
          if (hasClassHint) {{
            return true;
          }}
          if (isLikelyNodeText(node)) {{
            return false;
          }}
          const text = String(textValue || "").trim();
          const connectorVerbPattern =
            /(reads|writes|routes|uses|sends|requests|invokes|provides|streams|contains|ingests|maps|links|calls|normalizes|authenticates|downloads|publishes|interacts|generates|captures|processes)/i;
          if (
            fontSizePx > 0 &&
            fontSizePx <= 30 &&
            (connectorVerbPattern.test(text) || (text.length > 0 && text.length <= 64 && /\\s/.test(text)))
          ) {{
            return true;
          }}
          // Heuristic: small labels on open background are almost always edge labels.
          if (!localSample && fontSizePx > 0 && fontSizePx <= 21) {{
            return true;
          }}
          if (localSample && localSample.area > (svgArea * 0.08) && fontSizePx > 0 && fontSizePx <= 24) {{
            return true;
          }}
          return false;
        }};

        const ensureWhiteContrastForSample = (sample, minRatio = 5.4) => {{
          if (!sample || !Array.isArray(sample.rgb) || sample.rgb.length < 3) {{
            return;
          }}
          let current = sample.rgb;
          let ratio = contrastRatio(LIGHT_TEXT_RGB, current);
          if (ratio >= minRatio) {{
            return;
          }}
          for (let step = 0; step < 10 && ratio < minRatio; step += 1) {{
            current = darkenRgb(current, 0.07);
            ratio = contrastRatio(LIGHT_TEXT_RGB, current);
          }}
          sample.rgb = current;
          const cssColor = rgbToCss(current);
          sample.node.setAttribute("fill", cssColor);
          sample.node.style.fill = cssColor;
        }};

        const forceEdgeTextColor = (node) => {{
          if (node instanceof HTMLElement) {{
            node.style.setProperty("color", EDGE_TEXT, "important");
            node.style.setProperty("fill", EDGE_TEXT, "important");
            node.style.setProperty("opacity", "1", "important");
            return;
          }}
          if (node instanceof SVGElement) {{
            node.setAttribute("fill", EDGE_TEXT);
            node.style.setProperty("fill", EDGE_TEXT, "important");
            node.style.setProperty("opacity", "1", "important");
          }}
        }};

        // Force edge/connector label readability even when Mermaid/C4 emits
        // nested classes/styles that vary across versions.
        const edgeLabelSelectors = [
          "g.edgeLabel",
          "g.edgeLabel *",
          ".messageText",
          ".messageText *",
          ".relation",
          ".relation *",
          "[class*='edgeLabel'] text",
          "[class*='edgeLabel'] tspan",
          "[class*='edge-label'] text",
          "[class*='edge-label'] tspan",
          "[class*='relationshipLabel'] text",
          "[class*='relationshipLabel'] tspan",
          "[class*='relationLabel'] text",
          "[class*='relationLabel'] tspan",
          "[class*='messageText'] text",
          "[class*='messageText'] tspan",
          "[class*='linkLabel'] text",
          "[class*='linkLabel'] tspan",
        ];
        for (const selector of edgeLabelSelectors) {{
          const nodes = svg.querySelectorAll(selector);
          for (const node of nodes) {{
            forceEdgeTextColor(node);
          }}
        }}

        const textNodes = svg.querySelectorAll("text, tspan");
        for (const textNode of textNodes) {{
          if (!(textNode instanceof SVGGraphicsElement)) {{
            continue;
          }}
          const textValue = String(textNode.textContent || "").trim();
          if (!textValue) {{
            continue;
          }}
          let bbox = null;
          try {{
            bbox = textNode.getBBox();
          }} catch (_error) {{
            bbox = null;
          }}
          if (!bbox || bbox.width <= 0.2 || bbox.height <= 0.2) {{
            continue;
          }}
          const fontSizePx = parseNumber(getComputedStyle(textNode).fontSize, 0);
          const centerX = bbox.x + (bbox.width / 2);
          const centerY = bbox.y + (bbox.height / 2);
          const localSample = sampleAtPoint(centerX, centerY);
          if (isEdgeLikeText(textNode, localSample, fontSizePx, textValue)) {{
            forceEdgeTextColor(textNode);
            const edgeContainer = textNode.closest(
              ".edgeLabel, .messageText, .relation, g[class*='edge'], g[class*='relation'], g[class*='message']"
            );
            if (edgeContainer instanceof SVGElement) {{
              edgeContainer.style.opacity = "1";
            }}
            continue;
          }}
          const bgRgb = (localSample && localSample.rgb) || pageBgRgb;
          const labelColor = preferredTextColor(bgRgb);
          if (labelColor === LIGHT_TEXT && localSample) {{
            ensureWhiteContrastForSample(localSample);
          }}
          forceEdgeTextColor(textNode);
          textNode.setAttribute("fill", labelColor);
          textNode.style.setProperty("fill", labelColor, "important");
          textNode.style.setProperty("opacity", "1", "important");
          // Safety net: if text remains low-contrast against open background,
          // force the edge-label color.
          if (!localSample) {{
            const renderedFill = String(getComputedStyle(textNode).fill || "").trim();
            const renderedRgb = parseAnyColorRgb(renderedFill);
            if (renderedRgb && contrastRatio(renderedRgb, pageBgRgb) < 4.6) {{
              forceEdgeTextColor(textNode);
            }}
          }}
        }}

        const htmlTextNodes = svg.querySelectorAll("foreignObject span, foreignObject div, foreignObject p");
        for (const textNode of htmlTextNodes) {{
          if (!(textNode instanceof HTMLElement)) {{
            continue;
          }}
          const textValue = String(textNode.textContent || "").trim();
          if (!textValue) {{
            continue;
          }}
          const fontSizePx = parseNumber(getComputedStyle(textNode).fontSize, 0);
          const container = textNode.closest("foreignObject");
          let bgRgb = pageBgRgb;
          let localSample = null;
          if (container instanceof SVGGraphicsElement) {{
            let bbox = null;
            try {{
              bbox = container.getBBox();
            }} catch (_error) {{
              bbox = null;
            }}
            if (bbox && bbox.width > 0.2 && bbox.height > 0.2) {{
              const centerX = bbox.x + (bbox.width / 2);
              const centerY = bbox.y + (bbox.height / 2);
              localSample = sampleAtPoint(centerX, centerY);
              bgRgb = (localSample && localSample.rgb) || pageBgRgb;
            }}
          }}
          if (isEdgeLikeText(textNode, localSample, fontSizePx, textValue)) {{
            forceEdgeTextColor(textNode);
            continue;
          }}
          const labelColor = preferredTextColor(bgRgb);
          if (labelColor === LIGHT_TEXT && localSample) {{
            ensureWhiteContrastForSample(localSample);
          }}
          textNode.style.setProperty("color", labelColor, "important");
          textNode.style.setProperty("fill", labelColor, "important");
          textNode.style.setProperty("opacity", "1", "important");
          if (!localSample) {{
            const renderedColor = String(getComputedStyle(textNode).color || "").trim();
            const renderedRgb = parseAnyColorRgb(renderedColor);
            if (renderedRgb && contrastRatio(renderedRgb, pageBgRgb) < 4.6) {{
              forceEdgeTextColor(textNode);
            }}
          }}
        }}

        // Final pass: any small non-node labels with weak contrast on page
        // background are forced to the edge-label color.
        const finalSvgTextNodes = svg.querySelectorAll("text, tspan");
        for (const textNode of finalSvgTextNodes) {{
          if (!(textNode instanceof SVGGraphicsElement)) {{
            continue;
          }}
          const textValue = String(textNode.textContent || "").trim();
          if (!textValue) {{
            continue;
          }}
          if (isLikelyNodeText(textNode)) {{
            continue;
          }}
          const fontSizePx = parseNumber(getComputedStyle(textNode).fontSize, 0);
          if (fontSizePx <= 0 || fontSizePx > 32) {{
            continue;
          }}
          const renderedFill = String(getComputedStyle(textNode).fill || "").trim();
          const renderedRgb = parseAnyColorRgb(renderedFill);
          if (!renderedRgb) {{
            continue;
          }}
          if (contrastRatio(renderedRgb, pageBgRgb) < 4.8) {{
            forceEdgeTextColor(textNode);
          }}
        }}

        const finalHtmlTextNodes = svg.querySelectorAll("foreignObject span, foreignObject div, foreignObject p");
        for (const textNode of finalHtmlTextNodes) {{
          if (!(textNode instanceof HTMLElement)) {{
            continue;
          }}
          const textValue = String(textNode.textContent || "").trim();
          if (!textValue) {{
            continue;
          }}
          if (isLikelyNodeText(textNode)) {{
            continue;
          }}
          const fontSizePx = parseNumber(getComputedStyle(textNode).fontSize, 0);
          if (fontSizePx <= 0 || fontSizePx > 32) {{
            continue;
          }}
          const renderedColor = String(getComputedStyle(textNode).color || "").trim();
          const renderedRgb = parseAnyColorRgb(renderedColor);
          if (!renderedRgb) {{
            continue;
          }}
          if (contrastRatio(renderedRgb, pageBgRgb) < 4.8) {{
            forceEdgeTextColor(textNode);
          }}
        }}
      }};

      hardenGenericEdgesAndLabels();
      hardenNodeAndLabelContrast();

      const kind = String((block.dataset && block.dataset.mdexploreMermaidKind) || "").toLowerCase();
      const sourceTextForKind = String(
        (block.dataset && block.dataset.mdexploreMermaidSource) ||
        block.getAttribute("data-mdexplore-mermaid-source") ||
        ""
      );
      const sourceLooksLikeEr = /^\\s*erDiagram\\b/im.test(sourceTextForKind);
      if (sourceLooksLikeEr && block.dataset && !block.dataset.mdexploreMermaidKind) {{
        block.dataset.mdexploreMermaidKind = "er";
      }}
      const looksLikeRustErGeometry = (() => {{
        const parseSvgNumber = (rawValue, fallback = 0) => {{
          const parsed = Number.parseFloat(String(rawValue ?? "").trim());
          return Number.isFinite(parsed) ? parsed : fallback;
        }};
        // Rust ER SVGs do not always carry Mermaid's ER classes. Detect by
        // geometry: multiple large white table bodies + compact PK/FK pills.
        try {{
          const rects = Array.from(svg.querySelectorAll("rect"));
          let largeWhiteBodies = 0;
          let pkfkPills = 0;
          for (const rectNode of rects) {{
            if (!(rectNode instanceof SVGGraphicsElement)) {{
              continue;
            }}
            const fillText = String(
              rectNode.getAttribute("fill") || rectNode.style.fill || getComputedStyle(rectNode).fill || ""
            ).trim();
            const fillRgb = parseAnyColorRgb(fillText);
            if (!fillRgb) {{
              continue;
            }}
            let bbox = null;
            try {{
              bbox = rectNode.getBBox();
            }} catch (_error) {{
              bbox = null;
            }}
            if (!bbox || bbox.width <= 0.5 || bbox.height <= 0.5) {{
              continue;
            }}
            const rx = parseSvgNumber(rectNode.getAttribute("rx"), 0);
            const ry = parseSvgNumber(rectNode.getAttribute("ry"), 0);
            const lum = relativeLuminance(fillRgb);
            if (bbox.width >= 180 && bbox.height >= 80 && lum >= 0.84) {{
              largeWhiteBodies += 1;
            }}
            if (bbox.width <= 40 && bbox.height <= 22 && rx >= 6 && ry >= 6) {{
              pkfkPills += 1;
            }}
          }}
          return largeWhiteBodies >= 2 && pkfkPills >= 1;
        }} catch (_error) {{
          return false;
        }}
      }})();
      const looksLikeEr =
        kind === "er" ||
        sourceLooksLikeEr ||
        looksLikeRustErGeometry ||
        !!svg.querySelector(".entityBox, .relationshipLine, .relationshipLabelBox");
      if (!looksLikeEr) {{
        return;
      }}

      const hardenErRowsAndLabels = () => {{
        const evenRowFill = "#2b3f5f";
        const oddRowFill = "#223754";
        const strokeColor = "#93c5fd";
        const rowLabelColor = "#e5e7eb";

        const evenRowPaths = svg.querySelectorAll("g.row-rect-even > path:first-child");
        for (const pathNode of evenRowPaths) {{
          if (!(pathNode instanceof SVGElement)) {{
            continue;
          }}
          pathNode.setAttribute("fill", evenRowFill);
          pathNode.style.fill = evenRowFill;
          pathNode.setAttribute("stroke", strokeColor);
          pathNode.style.stroke = strokeColor;
        }}

        const oddRowPaths = svg.querySelectorAll("g.row-rect-odd > path:first-child");
        for (const pathNode of oddRowPaths) {{
          if (!(pathNode instanceof SVGElement)) {{
            continue;
          }}
          pathNode.setAttribute("fill", oddRowFill);
          pathNode.style.fill = oddRowFill;
          pathNode.setAttribute("stroke", strokeColor);
          pathNode.style.stroke = strokeColor;
        }}

        const rowBorderPaths = svg.querySelectorAll("g.row-rect-even > path, g.row-rect-odd > path");
        for (const pathNode of rowBorderPaths) {{
          if (!(pathNode instanceof SVGElement)) {{
            continue;
          }}
          pathNode.setAttribute("stroke", strokeColor);
          pathNode.style.stroke = strokeColor;
        }}

        const erLabelSelectors = [
          "g.label.name span.nodeLabel",
          "g.label.attribute-type span.nodeLabel",
          "g.label.attribute-name span.nodeLabel",
          "g.label.attribute-keys span.nodeLabel",
          "g.label.attribute-comment span.nodeLabel",
        ];
        for (const selector of erLabelSelectors) {{
          const nodes = svg.querySelectorAll(selector);
          for (const labelNode of nodes) {{
            if (!(labelNode instanceof HTMLElement)) {{
              continue;
            }}
            labelNode.style.color = rowLabelColor;
            labelNode.style.fill = rowLabelColor;
            labelNode.style.opacity = "1";
          }}
        }}

        const erTextSelectors = [
          "g.label.name text",
          "g.label.attribute-type text",
          "g.label.attribute-name text",
          "g.label.attribute-keys text",
          "g.label.attribute-comment text",
          "g.label.name tspan",
          "g.label.attribute-type tspan",
          "g.label.attribute-name tspan",
          "g.label.attribute-keys tspan",
          "g.label.attribute-comment tspan",
        ];
        for (const selector of erTextSelectors) {{
          const nodes = svg.querySelectorAll(selector);
          for (const textNode of nodes) {{
            if (!(textNode instanceof SVGElement)) {{
              continue;
            }}
            textNode.setAttribute("fill", rowLabelColor);
            textNode.style.fill = rowLabelColor;
            textNode.style.opacity = "1";
          }}
        }}

        // Rust Mermaid ER output uses plain <rect> blocks for entity bodies,
        // often with white fill. Darken those bodies in preview mode so the
        // existing light label colors remain readable.
        const entityBodyRects = [];
        const rectNodes = svg.querySelectorAll("rect");
        for (const rectNode of rectNodes) {{
          if (!(rectNode instanceof SVGGraphicsElement)) {{
            continue;
          }}
          if (rectNode.closest("defs, marker, symbol, .edgeLabel, .labelBkg, [class*='edgeLabel']")) {{
            continue;
          }}
          const classText = String(rectNode.getAttribute("class") || "").toLowerCase();
          if (classText.includes("edge") || classText.includes("label")) {{
            continue;
          }}
          const fillText = String(
            rectNode.getAttribute("fill") || rectNode.style.fill || getComputedStyle(rectNode).fill || ""
          ).trim();
          const fillRgb = parseAnyColorRgb(fillText);
          if (!fillRgb || relativeLuminance(fillRgb) < 0.84) {{
            continue;
          }}
          let bbox = null;
          try {{
            bbox = rectNode.getBBox();
          }} catch (_error) {{
            bbox = null;
          }}
          if (!bbox || bbox.width < 180 || bbox.height < 80) {{
            continue;
          }}
          entityBodyRects.push({{ node: rectNode, x: bbox.x, y: bbox.y }});
        }}

        if (entityBodyRects.length > 0) {{
          entityBodyRects.sort((a, b) => (a.y - b.y) || (a.x - b.x));
          const entityFills = [evenRowFill, oddRowFill];
          for (let index = 0; index < entityBodyRects.length; index += 1) {{
            const item = entityBodyRects[index];
            const fillColor = entityFills[index % entityFills.length];
            item.node.setAttribute("fill", fillColor);
            item.node.style.fill = fillColor;
            item.node.setAttribute("stroke", strokeColor);
            item.node.style.stroke = strokeColor;
          }}
        }}
      }};

      hardenErRowsAndLabels();
    }};

    window.__mdexploreApplyCachedMermaidSvg = async (entries, mode = "auto") => {{
      if (!Array.isArray(entries) || entries.length === 0) {{
        return 0;
      }}
      const batchSize = Math.max(1, {MERMAID_CACHE_RESTORE_BATCH_SIZE});
      let index = 0;
      while (index < entries.length) {{
        const end = Math.min(entries.length, index + batchSize);
        for (; index < end; index += 1) {{
          const item = entries[index];
          if (!item || !(item.block instanceof HTMLElement)) {{
            continue;
          }}
          const svgText = typeof item.svg === "string" ? item.svg : "";
          const block = item.block;
          if (svgText.indexOf("<svg") < 0) {{
            block.classList.remove("mermaid-pending");
            block.classList.add("mermaid-error");
            block.textContent = "Mermaid render failed: cached SVG missing";
            continue;
          }}
          block.removeAttribute("data-processed");
          block.removeAttribute("data-mdexplore-mermaid-render");
          block.classList.remove("mermaid-pending");
          block.classList.add("mermaid-ready");
          block.innerHTML = svgText;
          window.__mdexploreApplyMermaidPostStyles(block, mode);
        }}
        if (index < entries.length) {{
          await new Promise((resolve) => window.setTimeout(resolve, 0));
        }}
      }}
      return entries.length;
    }};

    window.__mdexploreTransformCallouts = () => {{
      const root = document.querySelector("main") || document.body;
      if (!root) {{
        return 0;
      }}
      const quotes = Array.from(root.querySelectorAll("blockquote"));
      if (!quotes.length) {{
        return 0;
      }}

      const titleByType = {{
        note: "Note",
        info: "Info",
        tip: "Tip",
        important: "Important",
        warning: "Warning",
        caution: "Caution",
      }};
      const iconByStyleType = {{
        note: "i",
        tip: "+",
        important: "!",
        warning: "!",
        caution: "!",
      }};
      const aliasByType = {{
        info: "note",
      }};

      const markerLineRegex = /^\\s*\\[!([A-Za-z0-9_-]+)\\]\\s*([+-])?(?:\\s+(.*))?\\s*$/;
      let transformed = 0;

      for (const quote of quotes) {{
        const firstBlock = quote.firstElementChild;
        if (!firstBlock) {{
          continue;
        }}
        const firstLine = ((firstBlock.textContent || "").split(/\\r?\\n/, 1)[0] || "").trim();
        const markerMatch = firstLine.match(markerLineRegex);
        if (!markerMatch) {{
          continue;
        }}

        const rawType = (markerMatch[1] || "note").trim().toLowerCase();
        const customTitle = (markerMatch[3] || "").trim();
        const normalizedType = aliasByType[rawType] || rawType;
        const styleType = {{
          note: "note",
          tip: "tip",
          important: "important",
          warning: "warning",
          caution: "caution",
        }}[normalizedType] || "note";
        const titleText =
          customTitle ||
          titleByType[rawType] ||
          titleByType[normalizedType] ||
          (rawType ? rawType.charAt(0).toUpperCase() + rawType.slice(1) : "Note");

        // Remove only the first marker line from leading text nodes while
        // preserving nested inline markup in the callout body.
        const firstBlockText = firstBlock.textContent || "";
        let charsToRemove = 0;
        const firstLineBoundary = firstBlockText.match(/^\\s*[^\\r\\n]*/);
        if (firstLineBoundary) {{
          charsToRemove = firstLineBoundary[0].length;
        }}
        const newlineBoundary = firstBlockText.slice(charsToRemove).match(/^\\r?\\n/);
        if (newlineBoundary) {{
          charsToRemove += newlineBoundary[0].length;
        }}

        if (charsToRemove > 0) {{
          const textWalker = document.createTreeWalker(firstBlock, NodeFilter.SHOW_TEXT);
          const textNodes = [];
          while (textWalker.nextNode()) {{
            textNodes.push(textWalker.currentNode);
          }}
          for (const node of textNodes) {{
            if (charsToRemove <= 0) {{
              break;
            }}
            const nodeText = node.nodeValue || "";
            if (nodeText.length <= charsToRemove) {{
              charsToRemove -= nodeText.length;
              node.nodeValue = "";
            }} else {{
              node.nodeValue = nodeText.slice(charsToRemove);
              charsToRemove = 0;
            }}
          }}
        }}

        // Drop leading blank text nodes and <br> left behind by marker stripping.
        while (firstBlock.firstChild && firstBlock.firstChild.nodeType === Node.TEXT_NODE) {{
          const value = firstBlock.firstChild.nodeValue || "";
          if (!value.trim()) {{
            firstBlock.removeChild(firstBlock.firstChild);
            continue;
          }}
          break;
        }}
        while (firstBlock.firstChild && firstBlock.firstChild.nodeType === Node.ELEMENT_NODE) {{
          const element = firstBlock.firstChild;
          if (element.tagName === "BR") {{
            firstBlock.removeChild(element);
            continue;
          }}
          break;
        }}

        const hasBodyText = ((firstBlock.textContent || "").trim().length > 0) || firstBlock.children.length > 0;
        if (!hasBodyText) {{
          firstBlock.remove();
        }}

        const callout = document.createElement("div");
        callout.className = "mdexplore-callout mdexplore-callout-" + styleType;
        callout.setAttribute("data-callout", rawType);
        for (const attrName of ["data-md-line-start", "data-md-line-end"]) {{
          if (quote.hasAttribute(attrName)) {{
            callout.setAttribute(attrName, quote.getAttribute(attrName) || "");
          }}
        }}

        const header = document.createElement("div");
        header.className = "mdexplore-callout-title";
        const icon = document.createElement("span");
        icon.className = "mdexplore-callout-icon";
        icon.setAttribute("aria-hidden", "true");
        icon.textContent = iconByStyleType[styleType] || "i";
        const label = document.createElement("span");
        label.className = "mdexplore-callout-title-text";
        label.textContent = titleText;
        header.appendChild(icon);
        header.appendChild(label);

        const body = document.createElement("div");
        body.className = "mdexplore-callout-content";
        while (quote.firstChild) {{
          body.appendChild(quote.firstChild);
        }}

        callout.appendChild(header);
        callout.appendChild(body);
        quote.replaceWith(callout);
        transformed += 1;
      }}

      return transformed;
    }};

    window.__mdexploreNormalizeMathText = () => {{
      // markdown-it treats \\# as an escape and can strip the backslash before
      // MathJax runs. Re-escape bare # inside $...$ / $$...$$ text so cardinality
      // expressions like #{{...}} remain valid TeX.
      const root = document.querySelector("main") || document.body;
      if (!root) {{
        return 0;
      }}

      const skipTags = new Set(["SCRIPT", "STYLE", "NOSCRIPT", "TEXTAREA", "PRE", "CODE"]);

      const escapeHashes = (mathText) => {{
        let out = "";
        for (let i = 0; i < mathText.length; i += 1) {{
          const ch = mathText[i];
          if (ch !== "#") {{
            out += ch;
            continue;
          }}
          const prev = i > 0 ? mathText[i - 1] : "";
          const next = i + 1 < mathText.length ? mathText[i + 1] : "";
          if (prev !== "\\\\" && !(next >= "0" && next <= "9")) {{
            out += "\\\\#";
          }} else {{
            out += ch;
          }}
        }}
        return out;
      }};

      const findClosingDouble = (text, start) => {{
        for (let i = start; i + 1 < text.length; i += 1) {{
          if (text[i] === "$" && text[i + 1] === "$" && (i === 0 || text[i - 1] !== "\\\\")) {{
            return i;
          }}
        }}
        return -1;
      }};

      const findClosingSingle = (text, start) => {{
        for (let i = start; i < text.length; i += 1) {{
          if (text[i] !== "$" || (i > 0 && text[i - 1] === "\\\\")) {{
            continue;
          }}
          // Treat $$ as double-delimiter, not the end of an inline span.
          if (i + 1 < text.length && text[i + 1] === "$") {{
            continue;
          }}
          return i;
        }}
        return -1;
      }};

      const normalizeNodeText = (text) => {{
        if (!text || text.indexOf("$") === -1 || text.indexOf("#") === -1) {{
          return text;
        }}
        let out = "";
        let i = 0;
        while (i < text.length) {{
          if (text[i] !== "$") {{
            out += text[i];
            i += 1;
            continue;
          }}

          if (i + 1 < text.length && text[i + 1] === "$") {{
            const end = findClosingDouble(text, i + 2);
            if (end < 0) {{
              out += text[i];
              i += 1;
              continue;
            }}
            const body = text.slice(i + 2, end);
            out += "$$" + escapeHashes(body) + "$$";
            i = end + 2;
            continue;
          }}

          const end = findClosingSingle(text, i + 1);
          if (end < 0) {{
            out += text[i];
            i += 1;
            continue;
          }}
          const body = text.slice(i + 1, end);
          out += "$" + escapeHashes(body) + "$";
          i = end + 1;
        }}
        return out;
      }};

      let updated = 0;
      const walker = document.createTreeWalker(
        root,
        NodeFilter.SHOW_TEXT,
        {{
          acceptNode(node) {{
            if (!node || !node.nodeValue || node.nodeValue.indexOf("$") === -1) {{
              return NodeFilter.FILTER_REJECT;
            }}
            const parent = node.parentElement;
            if (!parent || skipTags.has(parent.tagName)) {{
              return NodeFilter.FILTER_REJECT;
            }}
            return NodeFilter.FILTER_ACCEPT;
          }},
        }},
      );

      const nodes = [];
      while (walker.nextNode()) {{
        nodes.push(walker.currentNode);
      }}
      for (const node of nodes) {{
        const nextText = normalizeNodeText(node.nodeValue || "");
        if (nextText !== node.nodeValue) {{
          node.nodeValue = nextText;
          updated += 1;
        }}
      }}
      return updated;
    }};

    // Mermaid rendering has two very different backends:
    // - JS: client-side render and cache by mode
    // - Rust: server-side/pre-rendered SVG with optional JS fallback in GUI
    // This function keeps those forks isolated while still exposing one entry
    // point to the rest of the preview lifecycle.
    window.__mdexploreRunMermaidWithMode = async (mode = "auto", force = false) => {{
      const normalizedMode = String(mode || "").toLowerCase() === "pdf" ? "pdf" : "auto";
      const backend = String(window.__mdexploreMermaidBackend || "js").toLowerCase();
      if (backend === "rust") {{
        // Rust mode prefers pre-rendered SVG injected by Python. GUI mode can
        // optionally fall back to Mermaid JS if Rust output is unavailable.
        const mermaidBlocks = Array.from(document.querySelectorAll(".mermaid"));
        const fallbackBlocks = [];
        const disableRustJsFallback = !!window.__mdexploreDisableRustJsFallback;
        const cacheByMode = window.__mdexploreMermaidSvgCacheByMode;
        const modeCache =
          cacheByMode && typeof cacheByMode === "object" && cacheByMode[normalizedMode] && typeof cacheByMode[normalizedMode] === "object"
            ? cacheByMode[normalizedMode]
            : null;
        for (const block of mermaidBlocks) {{
          if (!(block instanceof HTMLElement)) {{
            continue;
          }}
          const hashKey = String(block.getAttribute("data-mdexplore-mermaid-hash") || "").trim().toLowerCase();
          const sourceText = ((block.dataset && block.dataset.mdexploreMermaidSource) || (block.textContent || "").trim());
          const mermaidKind = sourceText ? window.__mdexploreDetectMermaidKind(sourceText) : "";
          if (block.dataset) {{
            if (mermaidKind) {{
              block.dataset.mdexploreMermaidKind = mermaidKind;
            }} else if (block.dataset.mdexploreMermaidKind) {{
              delete block.dataset.mdexploreMermaidKind;
            }}
          }}
          if (normalizedMode === "pdf" && hashKey && modeCache && typeof modeCache[hashKey] === "string") {{
            // PDF mode must use the dedicated PDF cache so GUI palette tweaks
            // never leak into exported output.
            const cachedSvg = modeCache[hashKey];
            if (cachedSvg.indexOf("<svg") >= 0) {{
              block.innerHTML = cachedSvg;
              block.classList.remove("mermaid-pending", "mermaid-error", "mermaid-rust-fallback");
              block.classList.add("mermaid-ready");
              continue;
            }}
          }}
          if (normalizedMode !== "pdf" && force && hashKey && modeCache && typeof modeCache[hashKey] === "string") {{
            // Force-refresh in GUI mode still starts from cached auto SVG when
            // possible so a PDF round-trip can restore the preview quickly.
            const cachedSvg = modeCache[hashKey];
            if (cachedSvg.indexOf("<svg") >= 0) {{
              block.innerHTML = cachedSvg;
              block.classList.remove("mermaid-pending", "mermaid-error", "mermaid-rust-fallback");
              block.classList.add("mermaid-ready");
              window.__mdexploreApplyMermaidPostStyles(block, normalizedMode);
              continue;
            }}
          }}
          const hasSvg = !!block.querySelector("svg");
          block.classList.remove("mermaid-pending");
          if (hasSvg) {{
            block.classList.remove("mermaid-error");
            block.classList.add("mermaid-ready");
            if (normalizedMode !== "pdf") {{
              window.__mdexploreApplyMermaidPostStyles(block, normalizedMode);
            }}
          }} else {{
            if (sourceText) {{
              block.dataset.mdexploreMermaidSource = sourceText;
              if (normalizedMode === "pdf") {{
                block.classList.remove("mermaid-ready", "mermaid-pending");
                block.classList.add("mermaid-error");
                const rustError = (block.getAttribute("data-mdexplore-rust-error") || "").trim();
                block.textContent = rustError
                  ? `Mermaid render failed: Rust renderer: ${{rustError}}`
                  : "Mermaid render failed: Rust PDF SVG unavailable";
              }} else {{
                block.classList.remove("mermaid-ready", "mermaid-error");
                block.classList.add("mermaid-pending");
                block.textContent = "Mermaid rendering...";
                fallbackBlocks.push(block);
              }}
            }} else {{
              block.classList.remove("mermaid-ready");
              block.classList.add("mermaid-error");
            }}
          }}
        }}
        if (fallbackBlocks.length > 0 && disableRustJsFallback) {{
          for (const block of fallbackBlocks) {{
            if (!(block instanceof HTMLElement)) {{
              continue;
            }}
            const rustError = (block.getAttribute("data-mdexplore-rust-error") || "").trim();
            block.classList.remove("mermaid-pending", "mermaid-ready", "mermaid-rust-fallback");
            block.classList.add("mermaid-error");
            block.textContent = rustError
              ? `Mermaid render failed: Rust renderer: ${{rustError}}`
              : "Mermaid render failed: Rust renderer did not produce SVG";
          }}
        }} else if (fallbackBlocks.length > 0) {{
          try {{
            const loaded = await window.__mdexploreLoadMermaidScript();
            if (!loaded || !window.mermaid) {{
              throw new Error("Mermaid script failed to load for Rust fallback");
            }}
            const mermaidConfig = window.__mdexploreMermaidInitConfig(normalizedMode);
            mermaid.initialize(mermaidConfig);
            for (const block of fallbackBlocks) {{
              if (!(block instanceof HTMLElement)) {{
                continue;
              }}
              const sourceText = (block.dataset && block.dataset.mdexploreMermaidSource) || "";
              const rustError = (block.getAttribute("data-mdexplore-rust-error") || "").trim();
              if (!sourceText) {{
                block.classList.remove("mermaid-pending", "mermaid-ready");
                block.classList.add("mermaid-error");
                block.textContent = "Mermaid source unavailable";
                continue;
              }}
              try {{
                const renderId = `mdexplore_mermaid_rust_fallback_${{Date.now()}}_${{Math.random().toString(36).slice(2)}}`;
                const renderResult = await mermaid.render(renderId, sourceText);
                const svgMarkup =
                  renderResult && typeof renderResult === "object" && typeof renderResult.svg === "string"
                    ? renderResult.svg
                    : String(renderResult || "");
                if (!svgMarkup || svgMarkup.indexOf("<svg") < 0) {{
                  throw new Error("Mermaid returned empty SVG");
                }}
                block.innerHTML = svgMarkup;
                block.classList.remove("mermaid-pending", "mermaid-error", "mermaid-rust-fallback");
                block.classList.add("mermaid-ready");
                window.__mdexploreApplyMermaidPostStyles(block, normalizedMode);
              }} catch (renderError) {{
                block.classList.remove("mermaid-pending", "mermaid-ready");
                block.classList.add("mermaid-error");
                const jsMessage =
                  renderError && renderError.message ? renderError.message : String(renderError || "Unknown Mermaid error");
                const prefix = rustError ? `Rust renderer: ${{rustError}}; ` : "";
                block.textContent = `Mermaid render failed: ${{prefix}}JS fallback: ${{jsMessage}}`;
              }}
            }}
          }} catch (fallbackLoadError) {{
            const loadMessage =
              fallbackLoadError && fallbackLoadError.message
                ? fallbackLoadError.message
                : String(fallbackLoadError || "Mermaid fallback load failed");
            for (const block of fallbackBlocks) {{
              if (!(block instanceof HTMLElement)) {{
                continue;
              }}
              const rustError = (block.getAttribute("data-mdexplore-rust-error") || "").trim();
              const prefix = rustError ? `Rust renderer: ${{rustError}}; ` : "";
              block.classList.remove("mermaid-pending", "mermaid-ready");
              block.classList.add("mermaid-error");
              block.textContent = `Mermaid render failed: ${{prefix}}JS fallback load: ${{loadMessage}}`;
            }}
          }}
        }}
        window.__mdexploreMermaidReady = true;
        window.__mdexploreMermaidPaletteMode = normalizedMode;
        return true;
      }}
      if (
        !force &&
        window.__mdexploreMermaidReady &&
        window.__mdexploreMermaidPaletteMode === normalizedMode
      ) {{
        return window.__mdexploreMermaidReady;
      }}
      if (window.__mdexploreMermaidRenderPromise) {{
        if (window.__mdexploreMermaidRenderMode === normalizedMode) {{
          return await window.__mdexploreMermaidRenderPromise;
        }}
        try {{
          await window.__mdexploreMermaidRenderPromise;
        }} catch (_error) {{
          // Re-render attempt below with requested mode.
        }}
      }}
      window.__mdexploreMermaidAttempted = true;
      window.__mdexploreMermaidRenderMode = normalizedMode;
      // Only one JS Mermaid render pass should run at a time; later callers
      // await the in-flight promise instead of duplicating work.
      window.__mdexploreMermaidRenderPromise = (async () => {{
        try {{
          const loaded = await window.__mdexploreLoadMermaidScript();
          if (!loaded || !window.mermaid) {{
            throw new Error("Mermaid script failed to load from local/CDN sources");
          }}
          if (!window.__mdexploreMermaidSvgCacheByMode || typeof window.__mdexploreMermaidSvgCacheByMode !== "object") {{
            window.__mdexploreMermaidSvgCacheByMode = {{}};
          }}
          if (
            !window.__mdexploreMermaidSvgCacheByMode[normalizedMode] ||
            typeof window.__mdexploreMermaidSvgCacheByMode[normalizedMode] !== "object"
          ) {{
            window.__mdexploreMermaidSvgCacheByMode[normalizedMode] = {{}};
          }}
          const modeCache = window.__mdexploreMermaidSvgCacheByMode[normalizedMode];
          const mermaidBlocks = Array.from(document.querySelectorAll(".mermaid"));
          let hasRenderTargets = false;
          let renderFailures = 0;
          const cachedHydrateTargets = [];
          for (const block of mermaidBlocks) {{
            if (!(block instanceof HTMLElement)) {{
              continue;
            }}
            const hashKey = (block.getAttribute("data-mdexplore-mermaid-hash") || "").trim().toLowerCase();
            const existingSource = (block.dataset && block.dataset.mdexploreMermaidSource) || "";
            if (!existingSource) {{
              const rawSource = (block.textContent || "").trim();
              if (rawSource) {{
                block.dataset.mdexploreMermaidSource = rawSource;
              }}
            }}
            const sourceText = (block.dataset && block.dataset.mdexploreMermaidSource) || "";
            if (!sourceText) {{
              continue;
            }}
            const mermaidKind = window.__mdexploreDetectMermaidKind(sourceText);
            if (mermaidKind) {{
              block.dataset.mdexploreMermaidKind = mermaidKind;
            }} else if (block.dataset && block.dataset.mdexploreMermaidKind) {{
              delete block.dataset.mdexploreMermaidKind;
            }}
            if (!force && hashKey && typeof modeCache[hashKey] === "string" && modeCache[hashKey].indexOf("<svg") >= 0) {{
              block.removeAttribute("data-mdexplore-mermaid-render");
              block.classList.remove("mermaid-ready", "mermaid-error");
              block.classList.add("mermaid-pending");
              block.textContent = "Mermaid rendering...";
              cachedHydrateTargets.push({{ block, svg: modeCache[hashKey] }});
              continue;
            }}
            block.removeAttribute("data-processed");
            block.classList.remove("mermaid-ready", "mermaid-error", "mermaid-pending");
            block.setAttribute("data-mdexplore-mermaid-render", "1");
            block.textContent = sourceText;
            hasRenderTargets = true;
          }}
          const cachedHydratePromise = window.__mdexploreApplyCachedMermaidSvg(cachedHydrateTargets, normalizedMode);
          if (hasRenderTargets) {{
            const mermaidConfig = window.__mdexploreMermaidInitConfig(normalizedMode);
            mermaid.initialize(mermaidConfig);
            for (const block of mermaidBlocks) {{
              if (!(block instanceof HTMLElement)) {{
                continue;
              }}
              if (block.getAttribute("data-mdexplore-mermaid-render") !== "1") {{
                continue;
              }}
              const sourceText = (block.dataset && block.dataset.mdexploreMermaidSource) || "";
              const hashKey = (block.getAttribute("data-mdexplore-mermaid-hash") || "").trim().toLowerCase();
              try {{
                const renderId = `mdexplore_mermaid_${{Date.now()}}_${{Math.random().toString(36).slice(2)}}`;
                const renderResult = await mermaid.render(renderId, sourceText);
                const svgMarkup =
                  renderResult && typeof renderResult === "object" && typeof renderResult.svg === "string"
                    ? renderResult.svg
                    : String(renderResult || "");
                if (!svgMarkup || svgMarkup.indexOf("<svg") < 0) {{
                  throw new Error("Mermaid returned empty SVG");
                }}
                block.innerHTML = svgMarkup;
                block.removeAttribute("data-mdexplore-mermaid-render");
                block.classList.remove("mermaid-pending", "mermaid-error");
                block.classList.add("mermaid-ready");
                window.__mdexploreApplyMermaidPostStyles(block, normalizedMode);
                if (!hashKey) {{
                  continue;
                }}
                const svgNode = block.querySelector("svg");
                if (!svgNode || typeof svgNode.outerHTML !== "string") {{
                  continue;
                }}
                modeCache[hashKey] = svgNode.outerHTML;
              }} catch (renderError) {{
                renderFailures += 1;
                block.removeAttribute("data-mdexplore-mermaid-render");
                block.classList.remove("mermaid-pending", "mermaid-ready");
                block.classList.add("mermaid-error");
                const message =
                  renderError && renderError.message ? renderError.message : String(renderError || "Unknown Mermaid error");
                block.textContent = `Mermaid render failed: ${{message}}`;
              }}
            }}
          }}
          await cachedHydratePromise;
          if (!hasRenderTargets && cachedHydrateTargets.length === 0) {{
            window.__mdexploreMermaidReady = true;
            window.__mdexploreMermaidPaletteMode = normalizedMode;
            return true;
          }}
          window.__mdexploreMermaidSvgCacheByMode[normalizedMode] = modeCache;
          window.__mdexploreMermaidReady = true;
          window.__mdexploreMermaidPaletteMode = normalizedMode;
          if (renderFailures > 0) {{
            console.error(`mdexplore Mermaid render completed with ${{renderFailures}} error(s)`);
          }}
        }} catch (error) {{
          window.__mdexploreMermaidReady = false;
          window.__mdexploreMermaidPaletteMode = normalizedMode;
          console.error("mdexplore Mermaid render failed:", error);
        }} finally {{
          window.__mdexploreMermaidRenderPromise = null;
          window.__mdexploreMermaidRenderMode = "";
        }}
        return window.__mdexploreMermaidReady;
      }})();
      return await window.__mdexploreMermaidRenderPromise;
    }};

    window.__mdexploreRunMermaid = async () => {{
      return window.__mdexploreRunMermaidWithMode("auto", false);
    }};

    // Math typesetting is retried independently of Mermaid so one subsystem
    // failing or loading slowly does not stall the other.
    window.__mdexploreTryTypesetMath = async () => {{
      if (window.__mdexploreMathInFlight) {{
        return window.__mdexploreMathReady;
      }}
      window.__mdexploreMathInFlight = true;
      try {{
        window.__mdexploreNormalizeMathText();
        const loaded = await window.__mdexploreLoadMathJaxScript();
        if (!loaded) {{
          throw new Error("MathJax script failed to load from local/CDN sources");
        }}
        if (!(window.MathJax && MathJax.typesetPromise)) {{
          throw new Error("MathJax runtime not available yet");
        }}
        if (MathJax.startup && MathJax.startup.promise) {{
          await MathJax.startup.promise;
        }}
        await MathJax.typesetPromise();
        window.__mdexploreMathReady = true;
        window.__mdexploreMathError = "";
      }} catch (error) {{
        window.__mdexploreMathReady = false;
        window.__mdexploreMathError = (error && error.message) ? error.message : String(error);
        console.error("mdexplore MathJax render failed:", error);
      }} finally {{
        window.__mdexploreMathInFlight = false;
      }}
      return window.__mdexploreMathReady;
    }};

    window.__mdexploreScheduleMathRetries = () => {{
      // External script load timing can lag; retry shortly before giving up.
      for (const delayMs of [160, 420, 900, 1700]) {{
        window.setTimeout(() => {{
          if (!window.__mdexploreMathReady) {{
            window.__mdexploreTryTypesetMath();
          }}
        }}, delayMs);
      }}
    }};

    // Main preview bootstrap: normalize callouts, render Mermaid/PlantUML
    // affordances, then typeset math. PDF mode uses the same entry point with
    // a different Mermaid mode.
    window.__mdexploreRunClientRenderers = async (options = null) => {{
      if (window.__mdexploreTransformCallouts) {{
        window.__mdexploreTransformCallouts();
      }}
      const mermaidMode =
        options && typeof options === "object" && String(options.mermaidMode || "").toLowerCase() === "pdf"
          ? "pdf"
          : "auto";
      if (mermaidMode === "auto" && window.__mdexploreClearPdfExportMode) {{
        window.__mdexploreClearPdfExportMode();
      }}
      const forceMermaid = !!(
        options &&
        typeof options === "object" &&
        options.forceMermaid
      );
      // Keep Mermaid failures isolated so math rendering is never blocked.
      if (
        !window.__mdexploreMermaidReady ||
        window.__mdexploreMermaidPaletteMode !== mermaidMode ||
        forceMermaid
      ) {{
        await window.__mdexploreRunMermaidWithMode(mermaidMode, forceMermaid);
      }}
      if (window.__mdexploreApplyPlantUmlZoomControls) {{
        window.__mdexploreApplyPlantUmlZoomControls(mermaidMode);
      }}
      const mathReady = await window.__mdexploreTryTypesetMath();
      if (!mathReady) {{
        window.__mdexploreScheduleMathRetries();
      }}
    }};

    window.__mdexploreLoadMathJaxScript();
    if (String(window.__mdexploreMermaidBackend || "js").toLowerCase() !== "rust") {{
      window.__mdexploreLoadMermaidScript();
    }}
  </script>
</head>
<body>
  <main>{body}</main>
  <script>
    window.addEventListener('DOMContentLoaded', () => {{
      if (window.__mdexploreInstallScrollLineIndicator) {{
        window.__mdexploreInstallScrollLineIndicator();
      }}
      // Start client-side renderers once content is mounted.
      if (window.__mdexploreRunClientRenderers) {{
        window.__mdexploreRunClientRenderers();
      }}
    }});
  </script>
</body>
</html>
"""


class PreviewRenderWorkerSignals(QObject):
    """Signals emitted by background preview rendering workers."""

    finished = Signal(int, str, str, object, object, str)


class PreviewRenderWorker(QRunnable):
    """Render markdown HTML in a worker thread to keep UI responsive."""

    def __init__(self, path: Path, request_id: int):
        super().__init__()
        self.path = path
        self.request_id = request_id
        self.signals = PreviewRenderWorkerSignals()

    def run(self) -> None:
        try:
            # Keep this fully self-contained so it is safe to run off-thread and
            # so renderer state cannot leak across requests.
            resolved = self.path.resolve()
            stat = resolved.stat()
            markdown_text = resolved.read_text(encoding="utf-8", errors="replace")
            renderer = MarkdownRenderer()
            total_lines = MdExploreWindow._count_markdown_lines(markdown_text)
            html_doc = renderer.render_document(markdown_text, resolved.name, total_lines=total_lines)
            self.signals.finished.emit(
                self.request_id,
                str(resolved),
                html_doc,
                stat.st_mtime_ns,
                stat.st_size,
                "",
            )
        except Exception as exc:
            path_text = str(self.path)
            self.signals.finished.emit(self.request_id, path_text, "", 0, 0, str(exc))


class PlantUmlRenderWorkerSignals(QObject):
    """Signals emitted by background PlantUML render workers."""

    finished = Signal(str, str, str)


class PlantUmlRenderWorker(QRunnable):
    """Render one PlantUML source block to SVG data URI in background."""

    def __init__(self, hash_key: str, prepared_code: str, jar_path: Path | None, setup_issue: str | None):
        super().__init__()
        self.hash_key = hash_key
        self.prepared_code = prepared_code
        self.jar_path = jar_path
        self.setup_issue = setup_issue
        self.signals = PlantUmlRenderWorkerSignals()

    def run(self) -> None:
        # Fast-fail setup problems before spawning Java so the UI gets a useful
        # error quickly and worker threads are not wasted.
        if self.setup_issue is not None:
            self.signals.finished.emit(self.hash_key, "error", self.setup_issue)
            return
        if self.jar_path is None:
            self.signals.finished.emit(self.hash_key, "error", "plantuml.jar not available")
            return

        command = [
            "java",
            "-Djava.awt.headless=true",
            "-jar",
            str(self.jar_path),
            "-pipe",
            "-tsvg",
            "-charset",
            "UTF-8",
        ]

        try:
            # PlantUML is CPU-heavy and can block; run in worker threads and
            # return compact status payloads via Qt signals.
            result = subprocess.run(
                command,
                input=self.prepared_code,
                text=True,
                capture_output=True,
                check=False,
                timeout=20,
            )
        except subprocess.TimeoutExpired:
            self.signals.finished.emit(self.hash_key, "error", "Local PlantUML render timed out")
            return
        except Exception as exc:
            self.signals.finished.emit(self.hash_key, "error", f"Local PlantUML render failed: {exc}")
            return

        if result.returncode != 0:
            details = _extract_plantuml_error_details(result.stderr or "")
            self.signals.finished.emit(self.hash_key, "error", f"Local PlantUML render failed: {details}")
            return

        svg_text = (result.stdout or "").strip()
        if "<svg" not in svg_text.casefold():
            self.signals.finished.emit(self.hash_key, "error", "Local PlantUML did not return SVG output")
            return

        encoded_svg = base64.b64encode(svg_text.encode("utf-8")).decode("ascii")
        data_uri = f"data:image/svg+xml;base64,{encoded_svg}"
        self.signals.finished.emit(self.hash_key, "done", data_uri)


class PdfExportWorkerSignals(QObject):
    """Signals emitted by background PDF export workers."""

    finished = Signal(str, str)


class PdfExportWorker(QRunnable):
    """Apply footer page numbers and write exported PDF in background."""

    def __init__(self, output_path: Path, pdf_bytes: bytes, layout_hints: dict[str, object] | None = None):
        super().__init__()
        self.output_path = output_path
        self.pdf_bytes = pdf_bytes
        self.layout_hints = layout_hints if isinstance(layout_hints, dict) else {}
        self.signals = PdfExportWorkerSignals()

    def run(self) -> None:
        try:
            stamped_pdf = _stamp_pdf_page_numbers(self.pdf_bytes, self.layout_hints)
            self.output_path.write_bytes(stamped_pdf)
            self.signals.finished.emit(str(self.output_path), "")
        except Exception as exc:
            self.signals.finished.emit(str(self.output_path), str(exc))


class ViewTabBar(QTabBar):
    """Custom tab bar that paints dark-theme-friendly pastel tab backgrounds."""

    PASTEL_SEQUENCE = [
        "#8fb8ff",
        "#9fd8c9",
        "#d7b8ff",
        "#f6c89f",
        "#f4b8c9",
        "#c8d8a0",
        "#b5d5f4",
        "#e8c6a7",
    ]
    WIDTH_TEMPLATE_TEXT = "999999"
    MAX_LABEL_CHARS = 48
    WIDTH_SIDE_PADDING = 10
    POSITION_BAR_WIDTH = 26
    POSITION_BAR_HEIGHT = 8
    POSITION_BAR_TEXT_GAP = 7
    POSITION_BAR_SEGMENTS = 8

    def __init__(self, parent=None):
        super().__init__(parent)
        # Drag state is tracked here instead of relying on Qt's default drag
        # ghost so the whole tab, not just the close button, appears to move.
        self._drag_candidate_index = -1
        self._drag_start_pos = None
        self._dragging_index = -1
        self._dragging_tab_x = 0
        self._dragging_tab_offset_x = 0

    @staticmethod
    def _event_pos(event):
        """Return event position as QPoint across Qt6 API variants."""
        try:
            return event.position().toPoint()
        except Exception:
            return event.pos()

    def _is_close_button_hit(self, tab_index: int, pos) -> bool:
        """Detect whether a pointer position targets a tab close button."""
        button = self.tabButton(tab_index, QTabBar.ButtonPosition.RightSide)
        return bool(button is not None and button.isVisible() and button.geometry().contains(pos))

    def _set_all_close_buttons_visible(self, visible: bool) -> None:
        """Show/hide close buttons while custom drag ghost is active."""
        for index in range(self.count()):
            button = self.tabButton(index, QTabBar.ButtonPosition.RightSide)
            if button is not None:
                button.setVisible(visible)

    def _begin_tab_drag(self, tab_index: int, pos) -> None:
        """Start custom full-tab drag ghost for smoother visual feedback."""
        if tab_index < 0 or tab_index >= self.count():
            return
        rect = self.tabRect(tab_index)
        if not rect.isValid():
            return

        self._dragging_index = tab_index
        self._dragging_tab_offset_x = max(0, min(rect.width() - 1, pos.x() - rect.x()))
        self._dragging_tab_x = rect.x()
        self._set_all_close_buttons_visible(False)
        self.update()

    def _target_index_for_x(self, center_x: int) -> int:
        """Map cursor X position to closest insertion tab index."""
        if self.count() <= 0:
            return -1
        for index in range(self.count()):
            if center_x <= self.tabRect(index).center().x():
                return index
        return self.count() - 1

    def _update_tab_drag(self, pos) -> None:
        """Move drag ghost and reorder tabs as cursor crosses boundaries."""
        if self._dragging_index < 0:
            return
        self._dragging_tab_x = pos.x() - self._dragging_tab_offset_x
        target_index = self._target_index_for_x(pos.x())
        if target_index >= 0 and target_index != self._dragging_index:
            self.moveTab(self._dragging_index, target_index)
            self._dragging_index = target_index
        self.update()

    def _end_tab_drag(self) -> None:
        """Finish drag mode and restore normal close button visibility."""
        self._drag_candidate_index = -1
        self._drag_start_pos = None
        self._dragging_index = -1
        self._dragging_tab_x = 0
        self._dragging_tab_offset_x = 0
        self._set_all_close_buttons_visible(True)
        self.update()

    def mousePressEvent(self, event) -> None:  # noqa: N802
        """Record potential drag start while preserving regular tab behavior."""
        if event.button() == Qt.MouseButton.LeftButton:
            pos = self._event_pos(event)
            tab_index = self.tabAt(pos)
            if tab_index >= 0 and not self._is_close_button_hit(tab_index, pos):
                self._drag_candidate_index = tab_index
                self._drag_start_pos = pos
            else:
                self._drag_candidate_index = -1
                self._drag_start_pos = None
        else:
            self._drag_candidate_index = -1
            self._drag_start_pos = None
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event) -> None:  # noqa: N802
        """Drive custom tab drag animation and reorder behavior."""
        if (
            self._drag_candidate_index >= 0
            and self._drag_start_pos is not None
            and (event.buttons() & Qt.MouseButton.LeftButton)
        ):
            pos = self._event_pos(event)
            if self._dragging_index < 0:
                if (pos - self._drag_start_pos).manhattanLength() >= QApplication.startDragDistance():
                    self._begin_tab_drag(self._drag_candidate_index, pos)
            if self._dragging_index >= 0:
                self._update_tab_drag(pos)
                event.accept()
                return
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event) -> None:  # noqa: N802
        """End custom drag mode on release and continue normal processing."""
        if event.button() == Qt.MouseButton.LeftButton and self._dragging_index >= 0:
            self._end_tab_drag()
            super().mouseReleaseEvent(event)
            return
        self._drag_candidate_index = -1
        self._drag_start_pos = None
        super().mouseReleaseEvent(event)

    def _color_slot_for_index(self, tab_index: int) -> int:
        """Resolve palette slot from tab metadata, with sequence fallback."""
        palette_size = len(self.PASTEL_SEQUENCE)
        data = self.tabData(tab_index)
        if isinstance(data, dict):
            raw_slot = data.get("color_slot")
            try:
                slot = int(raw_slot)
            except Exception:
                slot = -1
            if 0 <= slot < palette_size:
                return slot
        sequence = self._sequence_for_index(tab_index)
        return (max(1, sequence) - 1) % palette_size

    def _sequence_for_index(self, tab_index: int) -> int:
        """Extract open-sequence index from tab data with backward compatibility."""
        data = self.tabData(tab_index)
        if isinstance(data, dict):
            raw = data.get("sequence")
            if isinstance(raw, int) and raw > 0:
                return raw
        if isinstance(data, int) and data > 0:
            return data
        return tab_index + 1

    def _base_color_for_index(self, tab_index: int) -> QColor:
        """Return base color for a tab from the configured pastel sequence."""
        color_slot = self._color_slot_for_index(tab_index)
        color_hex = self.PASTEL_SEQUENCE[color_slot]
        return QColor(color_hex)

    def _paint_single_tab(self, painter: QPainter, tab_index: int, rect, *, selected: bool, force_opaque: bool) -> None:
        """Paint one tab using shared logic for static and drag-ghost rendering."""
        base = self._base_color_for_index(tab_index)
        fill = QColor(base)
        if selected:
            fill = fill.lighter(107)
            if force_opaque:
                fill.setAlpha(255)
            else:
                fill.setAlpha(236)
            border = QColor(fill).darker(130)
        else:
            if force_opaque:
                fill.setAlpha(244)
            else:
                fill.setAlpha(172)
            border = QColor(fill).darker(155)

        painter.setPen(QPen(border, 1.1))
        painter.setBrush(fill)
        painter.drawRoundedRect(rect, 6.0, 6.0)

        # Draw a compact segmented bargraph at the left to indicate each
        # tab's approximate position within the current document.
        bar_x = rect.left() + self.WIDTH_SIDE_PADDING - 1
        bar_y = rect.center().y() - (self.POSITION_BAR_HEIGHT // 2)
        bar_w = self.POSITION_BAR_WIDTH
        bar_h = self.POSITION_BAR_HEIGHT
        track_fill = QColor("#1f2937" if selected else "#182233")
        if force_opaque:
            track_fill.setAlpha(236 if selected else 214)
        else:
            track_fill.setAlpha(188 if selected else 152)
        track_border = QColor("#314156")
        painter.setPen(QPen(track_border, 0.9))
        painter.setBrush(track_fill)
        painter.drawRoundedRect(bar_x, bar_y, bar_w, bar_h, 2.2, 2.2)

        inner_x = bar_x + 1
        inner_y = bar_y + 1
        inner_w = max(1, bar_w - 2)
        inner_h = max(1, bar_h - 2)
        segments = self.POSITION_BAR_SEGMENTS
        segment_gap = 1
        segment_w = max(1, (inner_w - ((segments - 1) * segment_gap)) // segments)
        used_w = (segment_w * segments) + ((segments - 1) * segment_gap)
        start_x = inner_x + max(0, (inner_w - used_w) // 2)
        progress = self._progress_for_index(tab_index)
        filled_segments = int(round(progress * segments))
        if progress > 0.0 and filled_segments <= 0:
            filled_segments = 1
        filled_segments = max(0, min(segments, filled_segments))
        segment_active = QColor(base).darker(116 if selected else 128)
        segment_inactive = QColor("#425066")
        if force_opaque:
            segment_inactive.setAlpha(148 if selected else 126)
        else:
            segment_inactive.setAlpha(115 if selected else 92)
        painter.setPen(Qt.PenStyle.NoPen)
        for segment_index in range(segments):
            segment_x = start_x + (segment_index * (segment_w + segment_gap))
            segment_color = segment_active if segment_index < filled_segments else segment_inactive
            painter.setBrush(segment_color)
            painter.drawRect(segment_x, inner_y, segment_w, inner_h)

        text_left = bar_x + bar_w + self.POSITION_BAR_TEXT_GAP
        text_rect = rect.adjusted(text_left - rect.left(), 0, -9, 0)
        close_button = self.tabButton(tab_index, QTabBar.ButtonPosition.RightSide)
        if close_button is not None and close_button.isVisible():
            text_rect.setRight(min(text_rect.right(), close_button.geometry().left() - 4))

        text_color = QColor("#0b1220" if selected else "#1b2436")
        if not self.isTabEnabled(tab_index):
            text_color.setAlpha(130)
        painter.setPen(text_color)
        painter.drawText(text_rect, Qt.AlignmentFlag.AlignCenter, self.tabText(tab_index))

    def _progress_for_index(self, tab_index: int) -> float:
        """Read normalized document-position progress (0..1) from tab metadata."""
        data = self.tabData(tab_index)
        if isinstance(data, dict):
            raw = data.get("progress")
            try:
                value = float(raw)
            except Exception:
                value = 0.0
            if math.isfinite(value):
                return max(0.0, min(1.0, value))
        return 0.0

    def _constant_tab_width(self) -> int:
        """Compute a stable tab width sized for six digits plus close button."""
        text_width = self.fontMetrics().horizontalAdvance(self.WIDTH_TEMPLATE_TEXT)
        close_width = 0
        if self.tabsClosable():
            close_width = self.style().pixelMetric(QStyle.PixelMetric.PM_TabCloseIndicatorWidth, None, self) + 8
        return (
            text_width
            + (self.WIDTH_SIDE_PADDING * 2)
            + self.POSITION_BAR_WIDTH
            + self.POSITION_BAR_TEXT_GAP
            + close_width
        )

    def _tab_width_for_text(self, text: str) -> int:
        """Return tab width for one label, bounded below by the default width."""
        text_width = self.fontMetrics().horizontalAdvance(text or self.WIDTH_TEMPLATE_TEXT)
        close_width = 0
        if self.tabsClosable():
            close_width = self.style().pixelMetric(QStyle.PixelMetric.PM_TabCloseIndicatorWidth, None, self) + 8
        dynamic_width = (
            text_width
            + (self.WIDTH_SIDE_PADDING * 2)
            + self.POSITION_BAR_WIDTH
            + self.POSITION_BAR_TEXT_GAP
            + close_width
        )
        return max(self._constant_tab_width(), dynamic_width)

    def tabSizeHint(self, index: int) -> QSize:  # noqa: N802
        """Return per-tab width, expanding for custom labels when needed."""
        base = super().tabSizeHint(index)
        return QSize(self._tab_width_for_text(self.tabText(index)), base.height())

    def minimumTabSizeHint(self, index: int) -> QSize:  # noqa: N802
        """Match minimum width to the rendered label width."""
        base = super().minimumTabSizeHint(index)
        return QSize(self._tab_width_for_text(self.tabText(index)), base.height())

    def paintEvent(self, event) -> None:  # noqa: N802
        """Draw rounded pastel tabs while preserving built-in tab close buttons."""
        del event
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)

        for tab_index in range(self.count()):
            if self._dragging_index >= 0 and tab_index == self._dragging_index:
                # Draw active dragged tab as a floating ghost after static tabs.
                continue
            rect = self.tabRect(tab_index).adjusted(2, 2, -2, -1)
            if rect.width() <= 2 or rect.height() <= 2:
                continue

            selected = tab_index == self.currentIndex()
            self._paint_single_tab(painter, tab_index, rect, selected=selected, force_opaque=False)

        if self._dragging_index >= 0 and self.count() > 0:
            current_rect = self.tabRect(max(0, min(self._dragging_index, self.count() - 1)))
            ghost_rect = current_rect.adjusted(2, 2, -2, -1)
            if ghost_rect.width() <= 2 or ghost_rect.height() <= 2:
                painter.end()
                return
            draw_y = max(2, current_rect.y() + 2)
            draw_x = int(self._dragging_tab_x + 2)
            max_x = max(2, self.width() - ghost_rect.width() - 2)
            draw_x = max(2, min(max_x, draw_x))
            ghost_rect.moveLeft(draw_x)
            ghost_rect.moveTop(draw_y)
            painter.save()
            painter.setPen(Qt.PenStyle.NoPen)
            painter.setBrush(QColor(5, 10, 18, 108))
            painter.drawRoundedRect(ghost_rect.adjusted(1, 1, 3, 3), 6.0, 6.0)
            selected = self._dragging_index == self.currentIndex()
            self._paint_single_tab(painter, self._dragging_index, ghost_rect, selected=selected, force_opaque=True)
            painter.restore()

        painter.end()


class MdExploreWindow(QMainWindow):
    MAX_DOCUMENT_VIEWS = 8
    VIEWS_FILE_NAME = ".mdexplore-views.json"
    HIGHLIGHT_COLORS = [
        ("Yellow", "#f5d34f"),
        ("Green", "#78d389"),
        ("Blue", "#7bb9ff"),
        ("Orange", "#f6a05f"),
        ("Purple", "#bb9df5"),
        ("Red", "#ef7d7d"),
    ]

    def __init__(
        self,
        root: Path,
        app_icon: QIcon,
        config_path: Path,
        mermaid_backend: str = MERMAID_BACKEND_JS,
        gpu_context_available: bool = False,
    ):
        super().__init__()
        # Persistent document/session state is split deliberately:
        # - cache: rendered HTML keyed by file + stat signature
        # - preview scrolls: per-run only
        # - document view sessions: per-run
        # - persisted view sessions: on-disk per-directory sidecars
        self.root = root.resolve()
        self.config_path = config_path
        self.renderer = MarkdownRenderer(mermaid_backend=mermaid_backend)
        self.current_file: Path | None = None
        self.last_directory_selection: Path | None = self.root
        self.cache: dict[str, tuple[int, int, str]] = {}
        self.current_match_files: list[Path] = []
        self._pending_preview_search_terms: list[str] = []
        self._pending_preview_search_close_groups: list[list[tuple[str, bool]]] = []
        self._render_pool = QThreadPool(self)
        self._render_pool.setMaxThreadCount(1)
        self._render_request_id = 0
        self._active_render_workers: set[PreviewRenderWorker] = set()
        self._plantuml_pool = QThreadPool(self)
        # Let independent PlantUML blocks render concurrently; keep a modest
        # upper bound to avoid CPU saturation on large documents.
        self._plantuml_pool.setMaxThreadCount(max(2, min(6, os.cpu_count() or 2)))
        self._pdf_pool = QThreadPool(self)
        self._pdf_pool.setMaxThreadCount(1)
        self._active_pdf_workers: set[PdfExportWorker] = set()
        self._pdf_export_in_progress = False
        self._pdf_export_source_key: str | None = None
        self._pending_pdf_layout_hints: dict[str, object] = {}
        # Global, in-process result cache for PlantUML blocks keyed by hash of
        # normalized source. This survives file navigation during this run.
        self._plantuml_results: dict[str, tuple[str, str]] = {}
        # Track active and dependent docs so completed jobs can invalidate only
        # affected cached HTML snapshots.
        self._plantuml_inflight: set[str] = set()
        self._plantuml_docs_by_hash: dict[str, set[str]] = {}
        self._plantuml_placeholders_by_doc: dict[str, dict[str, list[str]]] = {}
        self._active_plantuml_workers: set[PlantUmlRenderWorker] = set()
        # Per-file session scroll memory (not persisted to disk).
        self._preview_scroll_positions: dict[str, float] = {}
        # Signature of the currently previewed markdown file so we can detect
        # on-disk edits and auto-refresh when content changes externally.
        self._current_preview_signature_key: str | None = None
        self._current_preview_signature: tuple[int, int] | None = None
        self._preview_capture_enabled = False
        self._scroll_restore_block_until = 0.0
        self._view_states: dict[int, dict[str, float | int]] = {}
        self._active_view_id: int | None = None
        self._next_view_id = 1
        self._next_view_sequence = 1
        self._next_tab_color_index = 0
        self._mermaid_svg_cache_by_mode: dict[str, dict[str, str]] = {"auto": {}, "pdf": {}}
        # Per-document, in-memory diagram viewport state (zoom/pan) for this run.
        self._diagram_view_state_by_doc: dict[str, dict[str, dict[str, float | bool]]] = {}
        # In-memory per-document tab/view sessions for this app run only.
        self._document_view_sessions: dict[str, dict] = {}
        # Per-directory disk-backed view session cache loaded on demand from
        # .mdexplore-views.json files.
        self._persisted_view_sessions_by_dir: dict[str, dict[str, dict]] = {}
        self._document_line_counts: dict[str, int] = {}
        self._current_document_total_lines = 1
        self._preview_html_temp_files: deque[Path] = deque()
        self._view_line_probe_pending = False
        self._last_view_line_probe_at = 0.0
        self._match_input_text = ""
        # Search is debounced so filesystem/content scans do not run on every
        # keystroke while the user is still typing an expression.
        self.match_timer = QTimer(self)
        self.match_timer.setSingleShot(True)
        self.match_timer.setInterval(1000)
        self.match_timer.timeout.connect(self._run_match_search)
        self._scroll_capture_timer = QTimer(self)
        self._scroll_capture_timer.setInterval(200)
        self._scroll_capture_timer.timeout.connect(self._capture_current_preview_scroll)
        self._scroll_capture_timer.start()
        # Diagram view-state capture is kept separate from normal scroll capture
        # because Mermaid/PlantUML maintain their own zoom/pan state inside the
        # embedded page.
        self._diagram_state_capture_timer = QTimer(self)
        self._diagram_state_capture_timer.setInterval(250)
        self._diagram_state_capture_timer.timeout.connect(self._on_diagram_state_capture_tick)
        self._diagram_state_capture_timer.start()
        self._default_status_text = "Ready"
        self._gpu_context_available = bool(gpu_context_available)
        self._status_idle_timer = QTimer(self)
        self._status_idle_timer.setInterval(900)
        self._status_idle_timer.timeout.connect(self._ensure_non_empty_status_message)
        self._status_idle_timer.start()
        self._file_change_watch_timer = QTimer(self)
        self._file_change_watch_timer.setInterval(1200)
        self._file_change_watch_timer.timeout.connect(self._on_file_change_watch_tick)
        self._file_change_watch_timer.start()
        # Centered overlay for long-running preview restore operations.
        self._restore_overlay_expected_key: str | None = None
        self._restore_overlay_needs_math = False
        self._restore_overlay_needs_mermaid = False
        self._restore_overlay_needs_plantuml = False
        self._restore_overlay_deadline = 0.0
        self._restore_overlay_probe_inflight = False
        self._restore_overlay_probe_started_at = 0.0
        self._restore_overlay_pending_show = False
        self._restore_overlay_shown_at = 0.0
        self._restore_overlay_poll_timer = QTimer(self)
        self._restore_overlay_poll_timer.setInterval(170)
        self._restore_overlay_poll_timer.timeout.connect(self._check_restore_overlay_progress)
        self._restore_overlay_show_timer = QTimer(self)
        self._restore_overlay_show_timer.setSingleShot(True)
        self._restore_overlay_show_timer.setInterval(RESTORE_OVERLAY_SHOW_DELAY_MS)
        self._restore_overlay_show_timer.timeout.connect(self._show_restore_overlay_now)
        # Keep user-adjusted tree/preview pane widths for this app run.
        self._session_splitter_sizes: list[int] | None = None
        self._initial_split_applied = False

        self.setWindowTitle("mdexplore")
        self.setWindowIcon(app_icon)
        # Give the top control bar a bit more horizontal/vertical room by default.
        self.resize(1540, 980)

        # Use a custom QFileSystemModel so highlight colors render directly
        # in the tree and persist beside files in each directory.
        self.model = ColorizedMarkdownModel(self)
        self.model.setFilter(QDir.AllDirs | QDir.NoDotAndDotDot | QDir.Files)
        self.model.setNameFilters(["*.md"])
        self.model.setNameFilterDisables(False)

        self.tree = QTreeView()
        self.tree.setModel(self.model)
        self.tree.setItemDelegate(MarkdownTreeItemDelegate(self.tree))
        self.tree.setIconSize(ColorizedMarkdownModel.decorated_icon_size())
        self.tree.setHeaderHidden(True)
        self.tree.hideColumn(1)
        self.tree.hideColumn(2)
        self.tree.hideColumn(3)
        self.tree.setColumnWidth(0, 340)
        self.tree.setMinimumWidth(240)
        self.tree.setMaximumWidth(700)
        self.tree.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.tree.customContextMenuRequested.connect(self._show_tree_context_menu)
        self.tree.selectionModel().currentChanged.connect(self._on_tree_selection_changed)
        self.tree.expanded.connect(self._on_tree_directory_expanded)

        self.preview = QWebEngineView()
        # Preview pages are loaded as local HTML. Allow remote JS/CSS so CDN
        # assets (MathJax/Mermaid) can load and render as expected.
        preview_settings = self.preview.settings()
        preview_settings.setAttribute(QWebEngineSettings.WebAttribute.LocalContentCanAccessRemoteUrls, True)
        preview_settings.setAttribute(QWebEngineSettings.WebAttribute.LocalContentCanAccessFileUrls, True)
        if hasattr(QWebEngineSettings.WebAttribute, "PrintElementBackgrounds"):
            # Keep PDF output visually closer to what users see in the preview.
            preview_settings.setAttribute(QWebEngineSettings.WebAttribute.PrintElementBackgrounds, True)
        self.preview.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.preview.customContextMenuRequested.connect(self._show_preview_context_menu)
        self.preview.loadFinished.connect(self._on_preview_load_finished)

        self.view_tabs = ViewTabBar()
        self.view_tabs.setDocumentMode(True)
        self.view_tabs.setMovable(False)
        self.view_tabs.setDrawBase(False)
        self.view_tabs.setExpanding(False)
        self.view_tabs.setUsesScrollButtons(True)
        self.view_tabs.setTabsClosable(True)
        self.view_tabs.setElideMode(Qt.TextElideMode.ElideNone)
        self.view_tabs.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.view_tabs.currentChanged.connect(self._on_view_tab_changed)
        self.view_tabs.tabCloseRequested.connect(self._on_view_tab_close_requested)
        self.view_tabs.customContextMenuRequested.connect(self._show_view_tab_context_menu)
        self.view_tabs.setVisible(False)
        self._reset_document_views()
        self._refresh_tree_multi_view_markers()

        # Top-left document controls operate on directory scope and current file
        # scope; the right side hosts clipboard/search operations.
        self.up_btn = QPushButton("^")
        self.up_btn.clicked.connect(self._go_up_directory)

        refresh_btn = QPushButton("Refresh")
        refresh_btn.clicked.connect(self._refresh_directory_view)

        self.pdf_btn = QPushButton("PDF")
        self.pdf_btn.clicked.connect(self._export_current_preview_pdf)

        self.add_view_btn = QPushButton("Add View")
        self.add_view_btn.clicked.connect(self._add_document_view)

        edit_btn = QPushButton("Edit")
        edit_btn.clicked.connect(self._edit_current_file)

        self.path_label = QLabel("")
        self.path_label.setTextInteractionFlags(self.path_label.textInteractionFlags())

        copy_label = QLabel("Copy to clipboard:")
        copy_buttons_widget = QWidget()
        copy_buttons_layout = QHBoxLayout(copy_buttons_widget)
        copy_buttons_layout.setContentsMargins(0, 0, 0, 0)
        copy_buttons_layout.setSpacing(4)
        copy_buttons_layout.addWidget(copy_label)

        copy_current_btn = QPushButton("")
        copy_current_btn.setFixedSize(18, 18)
        copy_current_btn.setToolTip("Copy currently previewed markdown file")
        copy_current_btn.setStyleSheet("border: 1px solid #4b5563; border-radius: 3px; padding: 0px;")
        pin_icon_path = Path(__file__).resolve().parent / "pin.png"
        if pin_icon_path.is_file():
            pin_icon = QIcon(str(pin_icon_path))
            copy_current_btn.setIcon(pin_icon)
            copy_current_btn.setIconSize(QSize(16, 16))
        else:
            copy_current_btn.setText("P")
        copy_current_btn.clicked.connect(self._copy_current_preview_file_to_clipboard)
        copy_buttons_layout.addWidget(copy_current_btn)

        for color_name, color_value in self.HIGHLIGHT_COLORS:
            color_btn = QPushButton("")
            color_btn.setFixedSize(18, 18)
            color_btn.setToolTip(f"Copy files highlighted with {color_name.lower()}")
            color_btn.setStyleSheet(
                f"background-color: {color_value}; border: 1px solid #4b5563; border-radius: 3px;"
            )
            color_btn.clicked.connect(
                lambda _checked=False, c=color_value, n=color_name: self._copy_highlighted_files_to_clipboard(c, n)
            )
            copy_buttons_layout.addWidget(color_btn)

        # Search UI stays in the toolbar so tree filtering/highlighting remains
        # visible while the preview reacts in the right pane.
        match_label = QLabel("Search and highlight: ")
        self.match_input = QLineEdit()
        self.match_input.setClearButtonEnabled(False)
        self.match_input.setPlaceholderText('words, "quoted phrases", AND/OR/NOT, CLOSE(...)')
        self.match_input.setMinimumWidth(220)
        self.match_clear_action = self.match_input.addAction(
            _build_clear_x_icon(),
            QLineEdit.ActionPosition.TrailingPosition,
        )
        self.match_clear_action.setToolTip("Clear search")
        self.match_clear_action.triggered.connect(self._clear_match_input)
        self.match_clear_action.setVisible(False)
        self.match_input.textChanged.connect(self._on_match_text_changed)
        self.match_input.returnPressed.connect(self._run_match_search_now)

        match_buttons_widget = QWidget()
        match_buttons_layout = QHBoxLayout(match_buttons_widget)
        match_buttons_layout.setContentsMargins(0, 0, 0, 0)
        match_buttons_layout.setSpacing(4)
        match_buttons_layout.addWidget(match_label)
        match_buttons_layout.addWidget(self.match_input)
        for color_name, color_value in self.HIGHLIGHT_COLORS:
            color_btn = QPushButton("")
            color_btn.setFixedSize(18, 18)
            color_btn.setToolTip(f"Highlight current matches with {color_name.lower()}")
            color_btn.setStyleSheet(
                f"background-color: {color_value}; border: 1px solid #4b5563; border-radius: 3px;"
            )
            color_btn.clicked.connect(
                lambda _checked=False, c=color_value, n=color_name: self._apply_match_highlight_color(c, n)
            )
            match_buttons_layout.addWidget(color_btn)

        top_bar = QHBoxLayout()
        top_bar.setContentsMargins(0, 0, 0, 0)
        top_bar.addWidget(self.up_btn)
        top_bar.addWidget(refresh_btn)
        top_bar.addWidget(self.pdf_btn)
        top_bar.addWidget(self.add_view_btn)
        top_bar.addWidget(edit_btn)
        top_bar.addWidget(self.path_label, 1)
        top_bar.addWidget(copy_buttons_widget, 0, Qt.AlignmentFlag.AlignRight)
        top_bar.addSpacing(16)
        top_bar.addWidget(match_buttons_widget, 0, Qt.AlignmentFlag.AlignRight)

        top_bar_widget = QWidget()
        top_bar_widget.setLayout(top_bar)
        top_bar_widget.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        preview_container = QWidget()
        preview_layout = QVBoxLayout(preview_container)
        preview_layout.setContentsMargins(0, 0, 0, 0)
        preview_layout.setSpacing(0)
        preview_layout.addWidget(self.view_tabs)
        preview_layout.addWidget(self.preview, 1)

        self.splitter = QSplitter(Qt.Horizontal)
        self.splitter.addWidget(self.tree)
        self.splitter.addWidget(preview_container)
        self.splitter.setChildrenCollapsible(False)
        self.splitter.setStretchFactor(0, 1)
        self.splitter.setStretchFactor(1, 3)
        self.splitter.splitterMoved.connect(self._on_splitter_moved)

        central = QWidget()
        layout = QVBoxLayout(central)
        layout.addWidget(top_bar_widget)
        layout.addWidget(self.splitter, 1)

        self.setCentralWidget(central)
        self._restore_overlay = QLabel(
            "One moment please...",
            self,
        )
        self._restore_overlay.setObjectName("mdexplore-restore-overlay")
        self._restore_overlay.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self._restore_overlay.setWordWrap(True)
        self._restore_overlay.setStyleSheet(
            """
            QLabel#mdexplore-restore-overlay {
                background-color: rgba(147, 197, 253, 238);
                color: #000000;
                border: 1px solid #60a5fa;
                border-radius: 10px;
                padding: 10px 14px;
                font-weight: 600;
            }
            """
        )
        self._restore_overlay.hide()
        self._position_restore_overlay()
        self.statusBar().showMessage(self._default_status_text)
        self._gpu_status_label = QLabel("GPU")
        self._gpu_status_label.setStyleSheet("color: #9ca3af;")
        self._gpu_status_label.setVisible(self._gpu_context_available)
        self.statusBar().addPermanentWidget(self._gpu_status_label)
        backend_warning = self.renderer.mermaid_backend_warning()
        if backend_warning:
            self.statusBar().showMessage(
                f"Mermaid backend fallback to JS: {backend_warning}",
                7000,
            )
        # Root is initialized after widgets exist so view/model indexes are valid.
        self._set_root_directory(self.root)
        self._add_shortcuts()
        self.model.directoryLoaded.connect(self._maybe_apply_initial_split)
        QTimer.singleShot(0, self._maybe_apply_initial_split)

    def _add_shortcuts(self) -> None:
        """Register window-level keyboard shortcuts."""
        refresh_action = QAction("Refresh", self)
        refresh_action.setShortcut("F5")
        refresh_action.triggered.connect(self._refresh_directory_view)
        self.addAction(refresh_action)

    def resizeEvent(self, event) -> None:  # noqa: N802
        """Keep centered overlays aligned when the main window is resized."""
        super().resizeEvent(event)
        self._position_restore_overlay()

    def _position_restore_overlay(self) -> None:
        """Center the restore popup label within the visible window area."""
        if not hasattr(self, "_restore_overlay"):
            return
        available_width = max(320, self.width() - 80)
        target_width = min(760, available_width)
        self._restore_overlay.setFixedWidth(target_width)
        self._restore_overlay.adjustSize()
        x = max(20, (self.width() - self._restore_overlay.width()) // 2)
        y = max(20, (self.height() - self._restore_overlay.height()) // 2)
        self._restore_overlay.move(x, y)

    @staticmethod
    def _detect_special_features_from_markdown(markdown_text: str) -> tuple[bool, bool, bool]:
        """Return (has_math, has_mermaid, has_plantuml) from raw markdown."""
        text = markdown_text or ""
        has_mermaid = bool(re.search(r"(?im)^\s*```+\s*mermaid\b", text))
        has_plantuml = bool(re.search(r"(?im)^\s*```+\s*(?:plantuml|puml|uml)\b", text))
        has_math = bool(
            re.search(r"(?s)(?<!\\)\$\$(.+?)(?<!\\)\$\$", text)
            or re.search(r"(?<!\\)\$(?!\$)(?:[^$\n]|\\\$){1,400}?(?<!\\)\$", text)
        )
        return has_math, has_mermaid, has_plantuml

    @staticmethod
    def _detect_special_features_from_html(html_doc: str) -> tuple[bool, bool, bool]:
        """Return (has_math, has_mermaid, has_plantuml) from rendered HTML."""
        text = html_doc or ""
        has_mermaid = 'class="mermaid"' in text
        has_plantuml = ("plantuml-async" in text) or ('class="plantuml"' in text)
        has_math = (
            "mdexplore-math-block" in text
            or bool(re.search(r"(?<!\\)\$(?!\$)(?:[^$\n]|\\\$){1,400}?(?<!\\)\$", text))
            or bool(re.search(r"(?s)(?<!\\)\$\$(.+?)(?<!\\)\$\$", text))
        )
        return has_math, has_mermaid, has_plantuml

    def _detect_special_features_for_path(
        self,
        path: Path,
        *,
        cached_html: str | None = None,
    ) -> tuple[bool, bool, bool]:
        """Detect rich-render features from source markdown, with HTML fallback."""
        try:
            markdown_text = path.read_text(encoding="utf-8", errors="replace")
            return self._detect_special_features_from_markdown(markdown_text)
        except Exception:
            if cached_html is not None:
                return self._detect_special_features_from_html(cached_html)
            return (False, False, False)

    def _begin_restore_overlay_monitor(
        self,
        expected_key: str,
        *,
        needs_math: bool,
        needs_mermaid: bool,
        needs_plantuml: bool,
        phase: str,
    ) -> None:
        """Start delayed restore popup and readiness polling for rich previews."""
        # Disabled by request: this overlay could interfere with restore UX.
        self._stop_restore_overlay_monitor()
        return

    def _show_restore_overlay_now(self) -> None:
        """Show centered popup after delay if work is still in-flight."""
        if not self._restore_overlay_pending_show:
            return
        expected_key = self._restore_overlay_expected_key
        if not expected_key or self._current_preview_path_key() != expected_key:
            return
        self._position_restore_overlay()
        self._restore_overlay_shown_at = time.monotonic()
        self._restore_overlay.raise_()
        self._restore_overlay.show()

    def _stop_restore_overlay_monitor(self) -> None:
        """Stop restore polling and hide the centered progress popup."""
        self._restore_overlay_expected_key = None
        self._restore_overlay_needs_math = False
        self._restore_overlay_needs_mermaid = False
        self._restore_overlay_needs_plantuml = False
        self._restore_overlay_deadline = 0.0
        self._restore_overlay_probe_inflight = False
        self._restore_overlay_probe_started_at = 0.0
        self._restore_overlay_pending_show = False
        self._restore_overlay_shown_at = 0.0
        self._restore_overlay_show_timer.stop()
        self._restore_overlay_poll_timer.stop()
        if hasattr(self, "_restore_overlay"):
            self._restore_overlay.hide()

    def _check_restore_overlay_progress(self) -> None:
        """Poll current preview restore readiness and dismiss popup when ready."""
        expected_key = self._restore_overlay_expected_key
        if not expected_key:
            self._stop_restore_overlay_monitor()
            return
        if self._current_preview_path_key() != expected_key:
            self._stop_restore_overlay_monitor()
            return
        if time.monotonic() >= self._restore_overlay_deadline:
            self._stop_restore_overlay_monitor()
            return
        if self._restore_overlay_shown_at > 0.0:
            if (time.monotonic() - self._restore_overlay_shown_at) >= RESTORE_OVERLAY_MAX_VISIBLE_SECONDS:
                self._stop_restore_overlay_monitor()
                return

        plantuml_ready = True
        if self._restore_overlay_needs_plantuml:
            progress = self._preview_plantuml_progress()
            pending = bool(progress and progress[1] > 0)
            plantuml_ready = not pending

        needs_js_probe = self._restore_overlay_needs_math or self._restore_overlay_needs_mermaid
        if not needs_js_probe:
            if plantuml_ready:
                self._stop_restore_overlay_monitor()
            return
        if self._restore_overlay_probe_inflight:
            if (time.monotonic() - self._restore_overlay_probe_started_at) < 1.8:
                return
            # A prior JS callback can be dropped during rapid page switches.
            # Clear stale in-flight state and re-issue probe.
            self._restore_overlay_probe_inflight = False
            self._restore_overlay_probe_started_at = 0.0

        self._restore_overlay_probe_inflight = True
        self._restore_overlay_probe_started_at = time.monotonic()
        js = """
(() => {
  const hasMathNodes = !!document.querySelector(".mdexplore-math-block, mjx-container, .MathJax");
  const hasMermaidNodes = !!document.querySelector(".mermaid");
  return {
    hasMathNodes,
    hasMermaidNodes,
    mathReady: !hasMathNodes || !!window.__mdexploreMathReady,
    mermaidReady: !hasMermaidNodes || !!window.__mdexploreMermaidReady
  };
})();
"""
        self.preview.page().runJavaScript(
            js,
            lambda result, key=expected_key, plantuml_ok=plantuml_ready: self._on_restore_overlay_probe_result(
                key,
                plantuml_ok,
                result,
            ),
        )

    def _on_restore_overlay_probe_result(self, expected_key: str, plantuml_ready: bool, result) -> None:
        """Handle JS readiness probe for math/mermaid restore completion."""
        self._restore_overlay_probe_inflight = False
        self._restore_overlay_probe_started_at = 0.0
        if self._restore_overlay_expected_key != expected_key:
            return
        if self._current_preview_path_key() != expected_key:
            self._stop_restore_overlay_monitor()
            return
        if time.monotonic() >= self._restore_overlay_deadline:
            self._stop_restore_overlay_monitor()
            return

        math_ready = True
        mermaid_ready = True
        if self._restore_overlay_needs_math:
            math_ready = bool(isinstance(result, dict) and result.get("mathReady"))
        if self._restore_overlay_needs_mermaid:
            mermaid_ready = bool(isinstance(result, dict) and result.get("mermaidReady"))

        if math_ready and mermaid_ready and plantuml_ready:
            self._stop_restore_overlay_monitor()

    @staticmethod
    def _view_tab_label_for_line(line_number: int) -> str:
        """Return compact tab text for a view anchored near a source line."""
        return str(max(1, int(line_number)))

    @staticmethod
    def _normalize_custom_view_label(raw_value) -> str | None:
        """Normalize a custom tab label; blank resets, long labels are truncated."""
        if not isinstance(raw_value, str):
            return None
        if not raw_value.strip():
            return None
        cleaned = raw_value.replace("\r", " ").replace("\n", " ")
        if len(cleaned) > ViewTabBar.MAX_LABEL_CHARS:
            cleaned = cleaned[: ViewTabBar.MAX_LABEL_CHARS]
        return cleaned

    def _display_label_for_view(self, line_number: int, custom_label: str | None = None) -> str:
        """Return visible tab label, preferring a validated custom label override."""
        normalized = self._normalize_custom_view_label(custom_label)
        if normalized is not None:
            return normalized
        return self._view_tab_label_for_line(line_number)

    def _tab_custom_label(self, tab_index: int) -> str | None:
        """Read a tab's persisted custom label override from tab metadata."""
        if tab_index < 0 or tab_index >= self.view_tabs.count():
            return None
        data = self.view_tabs.tabData(tab_index)
        if not isinstance(data, dict):
            return None
        return self._normalize_custom_view_label(data.get("custom_label"))

    def _tab_label_anchor(self, tab_index: int) -> tuple[float, int] | None:
        """Read the saved custom-label bookmark for one tab, if present."""
        if tab_index < 0 or tab_index >= self.view_tabs.count():
            return None
        data = self.view_tabs.tabData(tab_index)
        if not isinstance(data, dict):
            return None
        if self._normalize_custom_view_label(data.get("custom_label")) is None:
            return None
        try:
            scroll_y = float(data.get("custom_label_anchor_scroll_y", 0.0))
        except Exception:
            scroll_y = 0.0
        try:
            top_line = max(1, int(data.get("custom_label_anchor_top_line", 1)))
        except Exception:
            top_line = 1
        if not math.isfinite(scroll_y):
            scroll_y = 0.0
        return scroll_y, top_line

    @staticmethod
    def _count_markdown_lines(markdown_text: str) -> int:
        """Return total source lines, treating empty content as one line."""
        return max(1, markdown_text.count("\n") + 1)

    @staticmethod
    def _line_progress(line_number: int, total_lines: int) -> float:
        """Convert top visible line number into normalized 0..1 document progress."""
        line_value = max(1, int(line_number))
        total_value = max(1, int(total_lines))
        if total_value <= 1:
            return 0.0
        return max(0.0, min(1.0, (line_value - 1) / (total_value - 1)))

    def _tab_view_id(self, tab_index: int) -> int | None:
        """Resolve a tab index into an internal view id."""
        if tab_index < 0 or tab_index >= self.view_tabs.count():
            return None
        try:
            value = self.view_tabs.tabData(tab_index)
            if value is None:
                return None
            if isinstance(value, dict):
                raw = value.get("view_id")
                if raw is None:
                    return None
                return int(raw)
            return int(value)
        except Exception:
            return None

    def _used_tab_color_slots(self) -> set[int]:
        """Collect palette slots currently assigned to open tabs."""
        used: set[int] = set()
        palette_size = len(ViewTabBar.PASTEL_SEQUENCE)
        for index in range(self.view_tabs.count()):
            data = self.view_tabs.tabData(index)
            if not isinstance(data, dict):
                continue
            raw_slot = data.get("color_slot")
            try:
                slot = int(raw_slot)
            except Exception:
                continue
            if 0 <= slot < palette_size:
                used.add(slot)
        return used

    def _allocate_next_tab_color_slot(self) -> int:
        """Pick next palette slot in rotation, skipping slots already in use."""
        palette_size = len(ViewTabBar.PASTEL_SEQUENCE)
        if palette_size <= 0:
            return 0
        used = self._used_tab_color_slots()
        start = self._next_tab_color_index % palette_size

        if len(used) < palette_size:
            for offset in range(palette_size):
                slot = (start + offset) % palette_size
                if slot in used:
                    continue
                self._next_tab_color_index = (slot + 1) % palette_size
                return slot

        # Fallback when every slot is occupied (should not happen with max views == palette size).
        slot = start
        self._next_tab_color_index = (slot + 1) % palette_size
        return slot

    def _current_view_state(self) -> dict[str, float | int] | None:
        """Return active view state dictionary when available."""
        if self._active_view_id is None:
            return None
        return self._view_states.get(self._active_view_id)

    def _save_document_view_session(
        self,
        path_key: str | None = None,
        *,
        capture_current: bool = True,
    ) -> None:
        """Snapshot current tab/view state for one document path key."""
        if path_key is None:
            path_key = self._current_preview_path_key()
        if not path_key:
            return

        if capture_current:
            self._capture_current_preview_scroll(force=True)

        sanitized_states: dict[int, dict[str, float | int]] = {}
        for raw_view_id, raw_state in self._view_states.items():
            try:
                view_id = int(raw_view_id)
            except Exception:
                continue
            if not isinstance(raw_state, dict):
                continue
            try:
                scroll_y = float(raw_state.get("scroll_y", 0.0))
            except Exception:
                scroll_y = 0.0
            if not math.isfinite(scroll_y):
                scroll_y = 0.0
            try:
                top_line = max(1, int(raw_state.get("top_line", 1)))
            except Exception:
                top_line = 1
            sanitized_states[view_id] = {"scroll_y": scroll_y, "top_line": top_line}

        palette_size = max(1, len(ViewTabBar.PASTEL_SEQUENCE))
        tabs: list[dict[str, int | float | str]] = []
        max_sequence = 0
        max_view_id = 0
        for index in range(self.view_tabs.count()):
            view_id = self._tab_view_id(index)
            if view_id is None:
                continue
            data = self.view_tabs.tabData(index)
            sequence = index + 1
            color_slot = (sequence - 1) % palette_size
            if isinstance(data, dict):
                raw_sequence = data.get("sequence")
                raw_color_slot = data.get("color_slot")
                custom_label = self._normalize_custom_view_label(data.get("custom_label"))
                try:
                    custom_label_anchor_scroll_y = float(data.get("custom_label_anchor_scroll_y", 0.0))
                except Exception:
                    custom_label_anchor_scroll_y = 0.0
                try:
                    custom_label_anchor_top_line = max(1, int(data.get("custom_label_anchor_top_line", 1)))
                except Exception:
                    custom_label_anchor_top_line = 1
                try:
                    sequence = max(1, int(raw_sequence))
                except Exception:
                    sequence = index + 1
                try:
                    color_slot = int(raw_color_slot)
                except Exception:
                    color_slot = (sequence - 1) % palette_size
            else:
                custom_label = None
                custom_label_anchor_scroll_y = 0.0
                custom_label_anchor_top_line = 1
            if color_slot < 0 or color_slot >= palette_size:
                color_slot = (sequence - 1) % palette_size
            state = sanitized_states.get(view_id)
            if state is None:
                state = {"scroll_y": 0.0, "top_line": 1}
                sanitized_states[view_id] = state
            tab_entry: dict[str, int | float | str] = {"view_id": view_id, "sequence": sequence, "color_slot": color_slot}
            if custom_label is not None:
                tab_entry["custom_label"] = custom_label
                if not math.isfinite(custom_label_anchor_scroll_y):
                    custom_label_anchor_scroll_y = 0.0
                tab_entry["custom_label_anchor_scroll_y"] = custom_label_anchor_scroll_y
                tab_entry["custom_label_anchor_top_line"] = custom_label_anchor_top_line
            tabs.append(tab_entry)
            max_sequence = max(max_sequence, sequence)
            max_view_id = max(max_view_id, view_id)

        active_view_id = self._active_view_id
        if active_view_id is None or all(entry["view_id"] != active_view_id for entry in tabs):
            current_index = self.view_tabs.currentIndex()
            active_view_id = self._tab_view_id(current_index)
        if active_view_id is None and tabs:
            active_view_id = tabs[0]["view_id"]

        next_view_id = max(self._next_view_id, max_view_id + 1)
        next_sequence = max(self._next_view_sequence, max_sequence + 1)
        try:
            next_color_index = int(self._next_tab_color_index) % palette_size
        except Exception:
            next_color_index = 0

        self._document_view_sessions[path_key] = {
            "view_states": sanitized_states,
            "tabs": tabs,
            "active_view_id": active_view_id,
            "next_view_id": next_view_id,
            "next_view_sequence": next_sequence,
            "next_tab_color_index": next_color_index,
        }

    @staticmethod
    def _clone_json_compatible_dict(payload: dict) -> dict:
        """Return a detached copy of a JSON-compatible dictionary."""
        try:
            cloned = json.loads(json.dumps(payload, ensure_ascii=False))
        except Exception:
            return {}
        return cloned if isinstance(cloned, dict) else {}

    @staticmethod
    def _path_directory_and_name(path_key: str | None) -> tuple[Path, str] | None:
        """Resolve a persisted path key into its directory and markdown filename."""
        if not isinstance(path_key, str) or not path_key:
            return None
        path = Path(path_key)
        name = path.name
        if not name:
            return None
        directory = path.parent
        try:
            directory = directory.resolve()
        except Exception:
            pass
        return directory, name

    def _views_file_path(self, directory: Path) -> Path:
        """Return the sidecar JSON path that stores persisted document views."""
        return directory / self.VIEWS_FILE_NAME

    def _directory_view_sessions(self, directory: Path) -> dict[str, dict]:
        """Load or return cached persisted view sessions for one directory."""
        try:
            resolved_directory = directory.resolve()
        except Exception:
            resolved_directory = directory
        directory_key = str(resolved_directory)
        cached = self._persisted_view_sessions_by_dir.get(directory_key)
        if cached is not None:
            return cached

        sessions: dict[str, dict] = {}
        file_path = self._views_file_path(resolved_directory)
        try:
            raw_payload = json.loads(file_path.read_text(encoding="utf-8"))
        except Exception:
            raw_payload = None

        file_map = raw_payload.get("files") if isinstance(raw_payload, dict) else raw_payload
        if isinstance(file_map, dict):
            for raw_name, raw_session in file_map.items():
                if not isinstance(raw_name, str) or not isinstance(raw_session, dict):
                    continue
                file_name = Path(raw_name).name
                if not file_name.lower().endswith(".md"):
                    continue
                cloned = self._clone_json_compatible_dict(raw_session)
                if cloned:
                    sessions[file_name] = cloned

        self._persisted_view_sessions_by_dir[directory_key] = sessions
        return sessions

    def _save_directory_view_sessions(self, directory: Path) -> None:
        """Persist one directory's view-session sidecar, failing quietly on IO errors."""
        try:
            resolved_directory = directory.resolve()
        except Exception:
            resolved_directory = directory
        directory_key = str(resolved_directory)
        sessions = self._persisted_view_sessions_by_dir.get(directory_key, {})
        file_path = self._views_file_path(resolved_directory)

        serializable_files: dict[str, dict] = {}
        if isinstance(sessions, dict):
            for file_name in sorted(sessions):
                raw_session = sessions.get(file_name)
                if not isinstance(file_name, str) or not isinstance(raw_session, dict):
                    continue
                cloned = self._clone_json_compatible_dict(raw_session)
                if cloned:
                    serializable_files[file_name] = cloned

        try:
            if not serializable_files:
                if file_path.exists():
                    file_path.unlink()
                return
            payload = {"files": serializable_files}
            file_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        except Exception:
            # View persistence is best-effort only and must not interrupt UI flow.
            pass

    @staticmethod
    def _should_persist_document_view_session(session: dict | None) -> bool:
        """Persist documents that have multi-view or custom-label state to restore."""
        if not isinstance(session, dict):
            return False
        tabs = session.get("tabs")
        if not isinstance(tabs, list):
            return False
        if len(tabs) > 1:
            return True
        for entry in tabs:
            if isinstance(entry, dict) and isinstance(entry.get("custom_label"), str) and entry.get("custom_label").strip():
                return True
        return False

    def _load_persisted_document_view_session(self, path_key: str) -> None:
        """Populate in-memory session cache from directory sidecar when needed."""
        if not path_key or path_key in self._document_view_sessions:
            return
        resolved = self._path_directory_and_name(path_key)
        if resolved is None:
            return
        directory, file_name = resolved
        session = self._directory_view_sessions(directory).get(file_name)
        if not isinstance(session, dict):
            return
        cloned = self._clone_json_compatible_dict(session)
        if cloned:
            self._document_view_sessions[path_key] = cloned

    def _persist_document_view_session(
        self,
        path_key: str | None = None,
        *,
        capture_current: bool = True,
    ) -> None:
        """Flush one document's in-memory view session snapshot into its directory sidecar."""
        if path_key is None:
            path_key = self._current_preview_path_key()
        if not path_key:
            return

        resolved = self._path_directory_and_name(path_key)
        if resolved is None:
            return
        directory, file_name = resolved

        self._save_document_view_session(path_key, capture_current=capture_current)
        sessions = self._directory_view_sessions(directory)
        session = self._document_view_sessions.get(path_key)
        if self._should_persist_document_view_session(session):
            sessions[file_name] = self._clone_json_compatible_dict(session)
        else:
            sessions.pop(file_name, None)
        self._save_directory_view_sessions(directory)
        self._refresh_tree_multi_view_markers()

    def _serialized_mermaid_cache_json(self) -> str:
        """Serialize in-memory Mermaid SVG cache for template injection."""
        try:
            return json.dumps(self._mermaid_svg_cache_by_mode, separators=(",", ":"), ensure_ascii=False)
        except Exception:
            return "{}"

    def _merge_renderer_pdf_mermaid_cache_seed(self) -> None:
        """Merge latest renderer-produced Rust PDF Mermaid SVGs into runtime cache."""
        try:
            payload = self.renderer.take_last_mermaid_pdf_svg_by_hash()
        except Exception:
            return
        if not isinstance(payload, dict) or not payload:
            return

        target = self._mermaid_svg_cache_by_mode.setdefault("pdf", {})
        for raw_hash, raw_svg in payload.items():
            if not isinstance(raw_hash, str) or not isinstance(raw_svg, str):
                continue
            hash_key = raw_hash.strip().lower()
            if not re.fullmatch(r"[0-9a-f]{40}", hash_key):
                continue
            if "<svg" not in raw_svg.casefold():
                continue
            if len(raw_svg) > MERMAID_SVG_MAX_CHARS:
                continue
            target[hash_key] = raw_svg
        while len(target) > MERMAID_SVG_CACHE_MAX_ENTRIES:
            target.pop(next(iter(target)))

    def _serialized_diagram_view_state_json(self, path_key: str | None) -> str:
        """Serialize per-document diagram view state for HTML seed injection."""
        if not path_key:
            return "{}"
        payload = self._diagram_view_state_by_doc.get(path_key, {})
        if not isinstance(payload, dict):
            return "{}"
        try:
            return json.dumps(payload, separators=(",", ":"), ensure_ascii=False)
        except Exception:
            return "{}"

    def _inject_mermaid_cache_seed(self, html_doc: str, path_key: str | None = None) -> str:
        """Inject runtime cache/state payloads into HTML template seed tokens."""
        resolved_key = path_key if path_key is not None else self._current_preview_path_key()
        token_literal = json.dumps(MERMAID_CACHE_JSON_TOKEN)
        cache_literal = json.dumps(self._serialized_mermaid_cache_json())
        out = html_doc
        if token_literal in out:
            out = out.replace(token_literal, cache_literal, 1)

        state_token_literal = json.dumps(DIAGRAM_VIEW_STATE_JSON_TOKEN)
        state_literal = json.dumps(self._serialized_diagram_view_state_json(resolved_key))
        if state_token_literal in out:
            out = out.replace(state_token_literal, state_literal, 1)
        return out

    def _capture_current_diagram_view_state(self, expected_key: str | None = None) -> None:
        """Snapshot in-page diagram zoom/pan state into per-document runtime cache."""
        key = expected_key or self._current_preview_path_key()
        if key is None:
            return
        js = """
(() => {
  if (window.__mdexploreCollectDiagramViewState) {
    return window.__mdexploreCollectDiagramViewState();
  }
  return {};
})();
"""
        self.preview.page().runJavaScript(
            js,
            lambda result, path_key=key: self._on_diagram_view_state_snapshot(path_key, result),
        )

    def _reapply_diagram_view_state_for(self, expected_key: str) -> None:
        """Push cached diagram zoom/pan state into the active page and reapply."""
        if self._current_preview_path_key() != expected_key:
            return
        payload = self._diagram_view_state_by_doc.get(expected_key, {})
        if not isinstance(payload, dict) or not payload:
            return
        payload_json = json.dumps(payload, separators=(",", ":"), ensure_ascii=False)
        js = f"""
(() => {{
  const incoming = {payload_json};
  if (!incoming || typeof incoming !== "object") {{
    return 0;
  }}
  if (!window.__mdexploreDiagramViewState || typeof window.__mdexploreDiagramViewState !== "object") {{
    window.__mdexploreDiagramViewState = {{}};
  }}
  for (const [key, value] of Object.entries(incoming)) {{
    window.__mdexploreSetDiagramViewState(key, value || {{}});
  }}
  let applied = 0;
  for (const shell of Array.from(document.querySelectorAll(".mdexplore-mermaid-shell"))) {{
    const fn = shell && shell.__mdexploreReapplySavedState;
    if (typeof fn !== "function") {{
      continue;
    }}
    try {{
      fn();
      applied += 1;
    }} catch (_error) {{
      // Ignore per-shell restore failures.
    }}
  }}
  return applied;
}})();
"""
        self.preview.page().runJavaScript(js)

    def _capture_current_diagram_view_state_blocking(self, expected_key: str, timeout_ms: int = 300) -> None:
        """Synchronously capture diagram zoom/pan state before preview navigation."""
        if not expected_key or self._current_preview_path_key() != expected_key:
            return
        js = """
(() => {
  if (window.__mdexploreCollectDiagramViewState) {
    return window.__mdexploreCollectDiagramViewState();
  }
  return {};
})();
"""
        loop = QEventLoop(self)
        completed = {"done": False}

        def on_result(result) -> None:
            if completed["done"]:
                return
            completed["done"] = True
            self._on_diagram_view_state_snapshot(expected_key, result)
            if loop.isRunning():
                loop.quit()

        self.preview.page().runJavaScript(js, on_result)

        timeout_timer = QTimer(self)
        timeout_timer.setSingleShot(True)
        timeout_timer.timeout.connect(loop.quit)
        timeout_timer.start(max(40, int(timeout_ms)))
        loop.exec()
        timeout_timer.stop()
        if not completed["done"]:
            # Fall back to an async capture if the blocking window times out.
            self._capture_current_diagram_view_state(expected_key)

    def _on_diagram_state_capture_tick(self) -> None:
        """Periodically mirror diagram zoom/pan state into Python memory."""
        path_key = self._current_preview_path_key()
        if path_key is None:
            return
        self._capture_current_diagram_view_state(path_key)

    def _on_diagram_view_state_snapshot(self, path_key: str, result) -> None:
        """Merge diagram view state snapshot from JS into process cache."""
        if not isinstance(path_key, str) or not path_key:
            return
        if not isinstance(result, dict):
            return
        sanitized: dict[str, dict[str, float | bool]] = {}
        for raw_key, raw_state in result.items():
            if not isinstance(raw_key, str) or not isinstance(raw_state, dict):
                continue
            state_key = raw_key.strip()
            if not state_key or len(state_key) > 240:
                continue
            try:
                zoom = float(raw_state.get("zoom", 1.0))
            except Exception:
                zoom = 1.0
            try:
                scroll_left = float(raw_state.get("scrollLeft", 0.0))
            except Exception:
                scroll_left = 0.0
            try:
                scroll_top = float(raw_state.get("scrollTop", 0.0))
            except Exception:
                scroll_top = 0.0
            if not math.isfinite(zoom):
                zoom = 1.0
            if not math.isfinite(scroll_left):
                scroll_left = 0.0
            if not math.isfinite(scroll_top):
                scroll_top = 0.0
            sanitized[state_key] = {
                "zoom": max(0.2, min(8.0, zoom)),
                "scrollLeft": max(0.0, scroll_left),
                "scrollTop": max(0.0, scroll_top),
                "dirty": bool(raw_state.get("dirty")),
            }
        existing = self._diagram_view_state_by_doc.get(path_key, {})
        if not sanitized:
            # Ignore transient empty snapshots (for example during page
            # teardown/navigation) so a good saved zoom/pan state is not lost.
            if isinstance(existing, dict) and existing:
                return
            self._diagram_view_state_by_doc[path_key] = {}
            return
        merged: dict[str, dict[str, float | bool]] = {}
        if isinstance(existing, dict):
            for existing_key, existing_state in existing.items():
                if isinstance(existing_key, str) and isinstance(existing_state, dict):
                    merged[existing_key] = existing_state
        merged.update(sanitized)
        self._diagram_view_state_by_doc[path_key] = merged

    def _schedule_mermaid_cache_harvest_for(self, expected_key: str) -> None:
        """Collect Mermaid SVG cache snapshots after client rendering settles."""
        for delay_ms in (380, 980, 2100):
            QTimer.singleShot(delay_ms, lambda key=expected_key: self._harvest_mermaid_cache_for(key))

    def _harvest_mermaid_cache_for(self, expected_key: str) -> None:
        """Fetch Mermaid SVG cache snapshot from active preview page."""
        if self._current_preview_path_key() != expected_key:
            return
        js = """
(() => {
  const cache = window.__mdexploreMermaidSvgCacheByMode;
  if (!cache || typeof cache !== "object") {
    return {};
  }
  return cache;
})();
"""
        self.preview.page().runJavaScript(
            js,
            lambda result, key=expected_key: self._on_mermaid_cache_snapshot(key, result),
        )

    def _on_mermaid_cache_snapshot(self, expected_key: str, result) -> None:
        """Merge Mermaid SVG cache snapshot from JS into Python process cache."""
        if self._current_preview_path_key() != expected_key:
            return
        if not isinstance(result, dict):
            return
        for mode_name in ("auto", "pdf"):
            mode_payload = result.get(mode_name)
            if not isinstance(mode_payload, dict):
                continue
            target = self._mermaid_svg_cache_by_mode.setdefault(mode_name, {})
            for raw_hash, raw_svg in mode_payload.items():
                if not isinstance(raw_hash, str) or not isinstance(raw_svg, str):
                    continue
                hash_key = raw_hash.strip().lower()
                if not re.fullmatch(r"[0-9a-f]{40}", hash_key):
                    continue
                if "<svg" not in raw_svg.casefold():
                    continue
                if len(raw_svg) > MERMAID_SVG_MAX_CHARS:
                    continue
                target[hash_key] = raw_svg
            while len(target) > MERMAID_SVG_CACHE_MAX_ENTRIES:
                target.pop(next(iter(target)))

    def _restore_document_view_session(self, path_key: str) -> bool:
        """Restore tab/view state for one document if a session snapshot exists."""
        session = self._document_view_sessions.get(path_key)
        if not isinstance(session, dict):
            return False

        raw_states = session.get("view_states")
        raw_tabs = session.get("tabs")
        if not isinstance(raw_states, dict) or not isinstance(raw_tabs, list):
            return False

        view_states: dict[int, dict[str, float | int]] = {}
        for raw_view_id, raw_state in raw_states.items():
            try:
                view_id = int(raw_view_id)
            except Exception:
                continue
            if not isinstance(raw_state, dict):
                continue
            try:
                scroll_y = float(raw_state.get("scroll_y", 0.0))
            except Exception:
                scroll_y = 0.0
            if not math.isfinite(scroll_y):
                scroll_y = 0.0
            try:
                top_line = max(1, int(raw_state.get("top_line", 1)))
            except Exception:
                top_line = 1
            view_states[view_id] = {"scroll_y": scroll_y, "top_line": top_line}

        palette_size = max(1, len(ViewTabBar.PASTEL_SEQUENCE))
        normalized_tabs: list[dict[str, int | float | str]] = []
        seen_view_ids: set[int] = set()
        max_sequence = 0
        max_view_id = 0
        for entry in raw_tabs:
            if not isinstance(entry, dict):
                continue
            try:
                view_id = int(entry.get("view_id"))
            except Exception:
                continue
            if view_id in seen_view_ids:
                continue
            seen_view_ids.add(view_id)
            if view_id not in view_states:
                view_states[view_id] = {"scroll_y": 0.0, "top_line": 1}
            try:
                sequence = max(1, int(entry.get("sequence", len(normalized_tabs) + 1)))
            except Exception:
                sequence = len(normalized_tabs) + 1
            try:
                color_slot = int(entry.get("color_slot", (sequence - 1) % palette_size))
            except Exception:
                color_slot = (sequence - 1) % palette_size
            if color_slot < 0 or color_slot >= palette_size:
                color_slot = (sequence - 1) % palette_size
            normalized_entry: dict[str, int | float | str] = {"view_id": view_id, "sequence": sequence, "color_slot": color_slot}
            custom_label = self._normalize_custom_view_label(entry.get("custom_label"))
            if custom_label is not None:
                try:
                    custom_label_anchor_scroll_y = float(entry.get("custom_label_anchor_scroll_y", 0.0))
                except Exception:
                    custom_label_anchor_scroll_y = 0.0
                if not math.isfinite(custom_label_anchor_scroll_y):
                    custom_label_anchor_scroll_y = 0.0
                try:
                    custom_label_anchor_top_line = max(1, int(entry.get("custom_label_anchor_top_line", 1)))
                except Exception:
                    custom_label_anchor_top_line = 1
                normalized_entry["custom_label"] = custom_label
                normalized_entry["custom_label_anchor_scroll_y"] = custom_label_anchor_scroll_y
                normalized_entry["custom_label_anchor_top_line"] = custom_label_anchor_top_line
            normalized_tabs.append(normalized_entry)
            max_sequence = max(max_sequence, sequence)
            max_view_id = max(max_view_id, view_id)

        if not normalized_tabs:
            return False

        blocked = self.view_tabs.blockSignals(True)
        while self.view_tabs.count() > 0:
            self.view_tabs.removeTab(0)
        self._view_states = view_states

        total_lines = max(1, int(self._current_document_total_lines))
        for tab_entry in normalized_tabs:
            view_id = tab_entry["view_id"]
            state = self._view_states.get(view_id, {"scroll_y": 0.0, "top_line": 1})
            try:
                top_line = max(1, int(state.get("top_line", 1)))
            except Exception:
                top_line = 1
            custom_label = self._normalize_custom_view_label(tab_entry.get("custom_label"))
            progress = self._line_progress(top_line, total_lines)
            index = self.view_tabs.addTab(self._display_label_for_view(top_line, custom_label))
            self.view_tabs.setTabData(
                index,
                {
                    "view_id": view_id,
                    "sequence": tab_entry["sequence"],
                    "color_slot": tab_entry["color_slot"],
                    "progress": progress,
                    "custom_label": custom_label,
                    "custom_label_anchor_scroll_y": float(tab_entry.get("custom_label_anchor_scroll_y", 0.0)),
                    "custom_label_anchor_top_line": max(1, int(tab_entry.get("custom_label_anchor_top_line", top_line))),
                },
            )
            self.view_tabs.setTabToolTip(index, f"Top visible line: {top_line} / {total_lines}")

        try:
            wanted_active = int(session.get("active_view_id"))
        except Exception:
            wanted_active = normalized_tabs[0]["view_id"]
        if all(entry["view_id"] != wanted_active for entry in normalized_tabs):
            wanted_active = normalized_tabs[0]["view_id"]

        active_index = 0
        for index in range(self.view_tabs.count()):
            if self._tab_view_id(index) == wanted_active:
                active_index = index
                break
        self.view_tabs.setCurrentIndex(active_index)
        self._active_view_id = self._tab_view_id(active_index)

        try:
            next_view_id = int(session.get("next_view_id", max_view_id + 1))
        except Exception:
            next_view_id = max_view_id + 1
        try:
            next_sequence = int(session.get("next_view_sequence", max_sequence + 1))
        except Exception:
            next_sequence = max_sequence + 1
        try:
            next_color_index = int(session.get("next_tab_color_index", 0))
        except Exception:
            next_color_index = 0

        self._next_view_id = max(next_view_id, max_view_id + 1)
        self._next_view_sequence = max(next_sequence, max_sequence + 1)
        self._next_tab_color_index = next_color_index % palette_size
        self.view_tabs.blockSignals(blocked)
        self._sync_all_view_tab_progress()
        self._update_view_tabs_visibility()
        self._update_add_view_button_state()
        return True

    def _set_view_tab_line(self, view_id: int, line_number: int) -> None:
        """Update one tab label/tooltip to match its top visible line."""
        line_value = max(1, int(line_number))
        total_lines = max(1, int(self._current_document_total_lines))
        progress = self._line_progress(line_value, total_lines)
        for index in range(self.view_tabs.count()):
            if self._tab_view_id(index) != view_id:
                continue
            display_label = self._display_label_for_view(line_value, self._tab_custom_label(index))
            if self.view_tabs.tabText(index) != display_label:
                self.view_tabs.setTabText(index, display_label)
                self.view_tabs.updateGeometry()
            data = self.view_tabs.tabData(index)
            if isinstance(data, dict):
                updated_data = dict(data)
                updated_data["progress"] = progress
                self.view_tabs.setTabData(index, updated_data)
            self.view_tabs.setTabToolTip(index, f"Top visible line: {line_value} / {total_lines}")
            self.view_tabs.update(self.view_tabs.tabRect(index))
            break

    def _sync_all_view_tab_progress(self) -> None:
        """Refresh per-tab progress metadata against current document line count."""
        total_lines = max(1, int(self._current_document_total_lines))
        for index in range(self.view_tabs.count()):
            view_id = self._tab_view_id(index)
            if view_id is None:
                continue
            state = self._view_states.get(view_id)
            if state is None:
                line_value = 1
            else:
                try:
                    line_value = max(1, int(state.get("top_line", 1)))
                except Exception:
                    line_value = 1
            progress = self._line_progress(line_value, total_lines)
            data = self.view_tabs.tabData(index)
            display_label = self._display_label_for_view(line_value, self._tab_custom_label(index))
            if self.view_tabs.tabText(index) != display_label:
                self.view_tabs.setTabText(index, display_label)
            if isinstance(data, dict):
                updated_data = dict(data)
                updated_data["progress"] = progress
                self.view_tabs.setTabData(index, updated_data)
            self.view_tabs.setTabToolTip(index, f"Top visible line: {line_value} / {total_lines}")
        self.view_tabs.updateGeometry()
        self.view_tabs.update()

    def _current_preview_scroll_key(self) -> str | None:
        """Return scroll cache key for current file + active view."""
        path_key = self._current_preview_path_key()
        if path_key is None:
            return None
        view_id = self._active_view_id
        if view_id is None:
            return path_key
        return f"{path_key}::view:{view_id}"

    def _update_add_view_button_state(self) -> None:
        """Enable Add View only when a file is open and tab budget remains."""
        if not hasattr(self, "add_view_btn"):
            return
        can_add = self.current_file is not None and self.view_tabs.count() < self.MAX_DOCUMENT_VIEWS
        self.add_view_btn.setEnabled(can_add)

    def _update_view_tabs_visibility(self) -> None:
        """Show tab strip for multi-view docs, or for a single custom-labeled view."""
        if not hasattr(self, "view_tabs"):
            return
        visible = False
        if self.current_file is not None:
            if self.view_tabs.count() > 1:
                visible = True
            elif self.view_tabs.count() == 1 and self._tab_custom_label(0) is not None:
                visible = True
        self.view_tabs.setVisible(visible)

    def _create_document_view(self, scroll_y: float, top_line: int, *, make_current: bool) -> int:
        """Create a new view tab/state entry and optionally activate it."""
        view_id = self._next_view_id
        self._next_view_id += 1
        sequence = self._next_view_sequence
        self._next_view_sequence += 1
        color_slot = self._allocate_next_tab_color_slot()
        try:
            safe_scroll = float(scroll_y)
        except Exception:
            safe_scroll = 0.0
        if not math.isfinite(safe_scroll):
            safe_scroll = 0.0
        safe_line = max(1, int(top_line))
        self._view_states[view_id] = {"scroll_y": safe_scroll, "top_line": safe_line}
        total_lines = max(1, int(self._current_document_total_lines))
        progress = self._line_progress(safe_line, total_lines)

        tab_index = self.view_tabs.addTab(self._view_tab_label_for_line(safe_line))
        self.view_tabs.setTabData(
            tab_index,
            {
                "view_id": view_id,
                "sequence": sequence,
                "color_slot": color_slot,
                "progress": progress,
                "custom_label": None,
                "custom_label_anchor_scroll_y": 0.0,
                "custom_label_anchor_top_line": safe_line,
            },
        )
        self.view_tabs.setTabToolTip(tab_index, f"Top visible line: {safe_line} / {total_lines}")

        if make_current:
            blocked = self.view_tabs.blockSignals(True)
            self.view_tabs.setCurrentIndex(tab_index)
            self.view_tabs.blockSignals(blocked)
            self._active_view_id = view_id

        return view_id

    def _reset_document_views(self, initial_scroll: float = 0.0, initial_line: int = 1) -> None:
        """Reset per-document view tabs back to a single base view."""
        self._view_states.clear()
        self._active_view_id = None
        self._next_view_id = 1
        self._next_view_sequence = 1
        self._next_tab_color_index = 0
        self._view_line_probe_pending = False
        self._last_view_line_probe_at = 0.0

        blocked = self.view_tabs.blockSignals(True)
        while self.view_tabs.count() > 0:
            self.view_tabs.removeTab(0)
        self.view_tabs.blockSignals(blocked)
        self._create_document_view(initial_scroll, initial_line, make_current=True)
        self._update_view_tabs_visibility()
        self._update_add_view_button_state()

    def _add_document_view(self) -> None:
        """Create another view tab for the current document at current top line."""
        if self.current_file is None:
            self.statusBar().showMessage("Open a markdown file before adding a view", 3000)
            return
        if self.view_tabs.count() >= self.MAX_DOCUMENT_VIEWS:
            self.statusBar().showMessage(f"Maximum of {self.MAX_DOCUMENT_VIEWS} views reached", 3500)
            return

        self._capture_current_preview_scroll(force=True)
        current_state = self._current_view_state() or {"scroll_y": 0.0, "top_line": 1}
        scroll_y = float(current_state.get("scroll_y", 0.0))
        top_line = int(current_state.get("top_line", 1))
        new_view_id = self._create_document_view(scroll_y, top_line, make_current=False)

        for index in range(self.view_tabs.count()):
            if self._tab_view_id(index) != new_view_id:
                continue
            self.view_tabs.setCurrentIndex(index)
            break

        self._update_view_tabs_visibility()
        self._update_add_view_button_state()
        self._refresh_tree_multi_view_markers()
        self.statusBar().showMessage(
            f"Added view {self.view_tabs.count()} of {self.MAX_DOCUMENT_VIEWS} at line {top_line}",
            3000,
        )

    def _on_view_tab_close_requested(self, tab_index: int) -> None:
        """Close one saved view tab while keeping at least one active view."""
        if self.view_tabs.count() <= 1:
            if self._tab_custom_label(tab_index) is not None:
                view_id = self._tab_view_id(tab_index)
                if view_id is None:
                    return
                state = self._view_states.get(view_id) or {"scroll_y": 0.0, "top_line": 1}
                try:
                    top_line = max(1, int(state.get("top_line", 1)))
                except Exception:
                    top_line = 1
                data = self.view_tabs.tabData(tab_index)
                updated_data = dict(data) if isinstance(data, dict) else {"view_id": view_id}
                updated_data["custom_label"] = None
                updated_data["custom_label_anchor_scroll_y"] = 0.0
                updated_data["custom_label_anchor_top_line"] = top_line
                self.view_tabs.setTabData(tab_index, updated_data)
                self.view_tabs.setTabText(tab_index, self._display_label_for_view(top_line, None))
                self.view_tabs.updateGeometry()
                self.view_tabs.update()
                self._update_view_tabs_visibility()
                self._persist_document_view_session()
                self._refresh_tree_multi_view_markers()
                self.statusBar().showMessage("Closed labeled tab and returned to hidden default view", 3000)
                return
            self.statusBar().showMessage("At least one view must remain open", 2500)
            return

        view_id = self._tab_view_id(tab_index)
        if view_id is None:
            return

        self._capture_current_preview_scroll(force=True)
        self._view_states.pop(view_id, None)
        path_key = self._current_preview_path_key()
        if path_key is not None:
            self._preview_scroll_positions.pop(f"{path_key}::view:{view_id}", None)

        self.view_tabs.removeTab(tab_index)
        if self._active_view_id == view_id:
            self._active_view_id = self._tab_view_id(self.view_tabs.currentIndex())

        self._update_view_tabs_visibility()
        self._update_add_view_button_state()
        self._refresh_tree_multi_view_markers()

    def _on_view_tab_changed(self, tab_index: int) -> None:
        """Switch active view and restore its own saved scroll position."""
        new_view_id = self._tab_view_id(tab_index)
        if new_view_id is None:
            return

        previous_view_id = self._active_view_id
        if previous_view_id is not None and previous_view_id != new_view_id:
            self._capture_current_preview_scroll(force=True)
        self._active_view_id = new_view_id

        if self.current_file is None:
            self._update_add_view_button_state()
            return

        self._preview_capture_enabled = False
        self._scroll_restore_block_until = time.monotonic() + 0.9
        expected_key = self._current_preview_path_key()
        if expected_key is None:
            return

        QTimer.singleShot(0, lambda key=expected_key: self._restore_current_preview_scroll(key))
        QTimer.singleShot(180, lambda key=expected_key: self._restore_current_preview_scroll(key))
        QTimer.singleShot(520, lambda key=expected_key: self._restore_current_preview_scroll(key))
        QTimer.singleShot(900, lambda key=expected_key: self._enable_preview_scroll_capture_for(key))
        self._request_active_view_top_line_update(force=True)
        self._update_add_view_button_state()

    def _show_view_tab_context_menu(self, pos) -> None:
        """Offer custom-label editing for document view tabs."""
        tab_index = self.view_tabs.tabAt(pos)
        if tab_index < 0:
            return

        menu = QMenu(self)
        edit_action = menu.addAction("Edit Tab Label...")
        return_action = None
        if self._tab_label_anchor(tab_index) is not None:
            return_action = menu.addAction("Return to beginning")
        chosen = menu.exec(self.view_tabs.mapToGlobal(pos))
        if chosen != edit_action:
            if chosen == return_action:
                self._return_view_tab_to_beginning(tab_index)
            return
        self._edit_view_tab_label(tab_index)

    def _edit_view_tab_label(self, tab_index: int) -> None:
        """Prompt for a custom tab label; blank restores the dynamic line number."""
        if tab_index < 0 or tab_index >= self.view_tabs.count():
            return

        current_custom = self._tab_custom_label(tab_index) or ""
        label_text, accepted = QInputDialog.getText(
            self,
            "Edit Tab Label",
            "Enter a custom tab label (blank restores the line number):",
            text=current_custom,
        )
        if not accepted:
            return
        was_truncated = len(label_text) > ViewTabBar.MAX_LABEL_CHARS
        custom_label = self._normalize_custom_view_label(label_text)
        view_id = self._tab_view_id(tab_index)
        if view_id is None:
            return

        data = self.view_tabs.tabData(tab_index)
        updated_data = dict(data) if isinstance(data, dict) else {"view_id": view_id}
        previous_custom_label = self._normalize_custom_view_label(updated_data.get("custom_label"))
        anchor_scroll_y, anchor_top_line = self._tab_label_anchor(tab_index) or (0.0, 1)
        state = self._view_states.get(view_id) or {"scroll_y": 0.0, "top_line": 1}
        try:
            current_scroll_y = float(state.get("scroll_y", 0.0))
        except Exception:
            current_scroll_y = 0.0
        if not math.isfinite(current_scroll_y):
            current_scroll_y = 0.0
        try:
            current_top_line = max(1, int(state.get("top_line", 1)))
        except Exception:
            current_top_line = 1
        if custom_label is None:
            anchor_scroll_y = 0.0
            anchor_top_line = current_top_line
        elif previous_custom_label != custom_label:
            anchor_scroll_y = current_scroll_y
            anchor_top_line = current_top_line
        updated_data["custom_label"] = custom_label
        updated_data["custom_label_anchor_scroll_y"] = anchor_scroll_y
        updated_data["custom_label_anchor_top_line"] = anchor_top_line
        self.view_tabs.setTabData(tab_index, updated_data)

        try:
            top_line = max(1, int(state.get("top_line", 1)))
        except Exception:
            top_line = 1
        self.view_tabs.setTabText(tab_index, self._display_label_for_view(top_line, custom_label))
        self.view_tabs.updateGeometry()
        self.view_tabs.update()
        self._persist_document_view_session()
        if custom_label is None:
            self.statusBar().showMessage("Restored dynamic line-number tab label", 2500)
        elif was_truncated:
            self.statusBar().showMessage(
                f"Tab label updated and truncated to {ViewTabBar.MAX_LABEL_CHARS} characters",
                3000,
            )
        else:
            self.statusBar().showMessage(f"Tab label updated to '{custom_label}'", 2500)

    def _return_view_tab_to_beginning(self, tab_index: int) -> None:
        """Restore a custom-labeled view to the scroll position captured when labeled."""
        anchor = self._tab_label_anchor(tab_index)
        view_id = self._tab_view_id(tab_index)
        path_key = self._current_preview_path_key()
        if anchor is None or view_id is None or path_key is None:
            return

        anchor_scroll_y, anchor_top_line = anchor
        state = self._view_states.setdefault(view_id, {"scroll_y": 0.0, "top_line": 1})
        state["scroll_y"] = anchor_scroll_y
        state["top_line"] = anchor_top_line
        self._preview_scroll_positions[f"{path_key}::view:{view_id}"] = anchor_scroll_y
        self._set_view_tab_line(view_id, anchor_top_line)
        self._persist_document_view_session(path_key, capture_current=False)

        if self._active_view_id != view_id:
            self.view_tabs.setCurrentIndex(tab_index)
        expected_key = self._current_preview_path_key()
        if expected_key is not None:
            self._preview_capture_enabled = False
            self._scroll_restore_block_until = time.monotonic() + 0.8
            QTimer.singleShot(0, lambda key=expected_key: self._restore_current_preview_scroll(key))
            QTimer.singleShot(180, lambda key=expected_key: self._restore_current_preview_scroll(key))
            QTimer.singleShot(520, lambda key=expected_key: self._restore_current_preview_scroll(key))
            QTimer.singleShot(850, lambda key=expected_key: self._enable_preview_scroll_capture_for(key))
        self.statusBar().showMessage(f"Returned tab to labeled beginning at line {anchor_top_line}", 3000)

    def _request_active_view_top_line_update(self, force: bool = False) -> None:
        """Probe top-most visible source line and update active tab label."""
        if self.current_file is None or self._active_view_id is None:
            return
        now = time.monotonic()
        if not force:
            if self._view_line_probe_pending:
                return
            if now - self._last_view_line_probe_at < 0.35:
                return

        expected_key = self._current_preview_path_key()
        expected_view_id = self._active_view_id
        if expected_key is None:
            return

        self._view_line_probe_pending = True
        self._last_view_line_probe_at = now
        js = """
(() => {
  const probeX = Math.max(14, Math.floor(window.innerWidth * 0.42));
  const probeYs = [10, 20, 34, 50, 72, 96];
  for (const y of probeYs) {
    const el = document.elementFromPoint(probeX, y);
    if (!el) continue;
    const tagged = el.closest('[data-md-line-start]');
    if (!tagged) continue;
    const value = parseInt(tagged.getAttribute('data-md-line-start') || "", 10);
    if (!Number.isNaN(value)) return value + 1;
  }
  const taggedNodes = document.querySelectorAll('[data-md-line-start]');
  for (const node of taggedNodes) {
    const rect = node.getBoundingClientRect();
    if (rect.bottom < 0) continue;
    const value = parseInt(node.getAttribute('data-md-line-start') || "", 10);
    if (!Number.isNaN(value)) return value + 1;
  }
  return 1;
})();
"""
        self.preview.page().runJavaScript(
            js,
            lambda result, key=expected_key, view_id=expected_view_id: self._on_active_view_line_probe_result(
                key,
                view_id,
                result,
            ),
        )

    def _on_active_view_line_probe_result(self, expected_key: str, expected_view_id: int, result) -> None:
        """Apply top-line probe result to active view tab when still current."""
        self._view_line_probe_pending = False
        if self._current_preview_path_key() != expected_key:
            return
        if self._active_view_id != expected_view_id:
            return

        try:
            line_number = max(1, int(result))
        except Exception:
            line_number = 1

        state = self._view_states.get(expected_view_id)
        if state is None:
            return
        state["top_line"] = line_number
        self._set_view_tab_line(expected_view_id, line_number)

    def _placeholder_html(self, message: str) -> str:
        """Render an empty-state page in the preview pane."""
        escaped = html.escape(message)
        return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8"/>
  <style>
    html, body {{
      margin: 0;
      height: 100%;
      background: #0f172a;
      color: #cbd5e1;
      font-family: "Noto Sans", "DejaVu Sans", sans-serif;
    }}
    main {{
      height: 100%;
      display: grid;
      place-items: center;
      font-size: 1rem;
    }}
  </style>
</head>
<body><main>{escaped}</main></body>
</html>
"""

    @staticmethod
    def _html_with_base_href(html_doc: str, base_url: QUrl) -> str:
        """Inject `<base href=...>` so temp-file preview keeps relative links."""
        if not html_doc:
            return html_doc
        href = html.escape(base_url.toString(), quote=True)
        if not href:
            return html_doc
        closing_head = re.search(r"</head\s*>", html_doc, flags=re.IGNORECASE)
        if closing_head:
            head_content = html_doc[: closing_head.start()]
            if re.search(r"<base\s+[^>]*href=", head_content, flags=re.IGNORECASE):
                return html_doc
        open_head = re.search(r"<head\b[^>]*>", html_doc, flags=re.IGNORECASE)
        if not open_head:
            return html_doc
        base_tag = f'\n  <base href="{href}"/>'
        insert_at = open_head.end()
        return html_doc[:insert_at] + base_tag + html_doc[insert_at:]

    def _cleanup_preview_temp_files(self) -> None:
        """Delete temporary preview files used for oversized HTML payloads."""
        while self._preview_html_temp_files:
            path = self._preview_html_temp_files.popleft()
            try:
                path.unlink(missing_ok=True)
            except Exception:
                pass

    def _track_preview_temp_file(self, temp_path: Path) -> None:
        """Track temp preview files and clean up old entries eagerly."""
        self._preview_html_temp_files.append(temp_path)
        while len(self._preview_html_temp_files) > 6:
            stale = self._preview_html_temp_files.popleft()
            try:
                stale.unlink(missing_ok=True)
            except Exception:
                pass

    def _set_preview_html(self, html_doc: str, base_url: QUrl) -> None:
        """Load preview HTML with file-based fallback for large documents."""
        try:
            encoded_size = len(html_doc.encode("utf-8", errors="replace"))
        except Exception:
            encoded_size = len(html_doc)
        if encoded_size <= PREVIEW_SETHTML_MAX_BYTES:
            self.preview.setHtml(html_doc, base_url)
            return
        try:
            prepared = self._html_with_base_href(html_doc, base_url)
            temp_dir = Path(tempfile.gettempdir()) / "mdexplore-preview"
            temp_dir.mkdir(parents=True, exist_ok=True)
            with tempfile.NamedTemporaryFile(
                mode="w",
                encoding="utf-8",
                suffix=".html",
                prefix="preview-",
                dir=temp_dir,
                delete=False,
            ) as temp_file:
                temp_file.write(prepared)
                temp_path = Path(temp_file.name)
            self._track_preview_temp_file(temp_path)
            self.preview.load(QUrl.fromLocalFile(str(temp_path)))
            return
        except Exception:
            # If temp-file load setup fails, fall back to direct setHtml.
            self.preview.setHtml(html_doc, base_url)

    def _ensure_non_empty_status_message(self) -> None:
        """Keep a non-empty status bar message instead of blank idle periods."""
        current = self.statusBar().currentMessage().strip()
        if current:
            return
        self.statusBar().showMessage(self._default_status_text)

    def _preview_plantuml_progress(self) -> tuple[int, int, int] | None:
        """Return (done, pending, failed) PlantUML counts for current preview."""
        path_key = self._current_preview_path_key()
        if path_key is None:
            return None
        placeholders = self._plantuml_placeholders_by_doc.get(path_key, {})
        if not placeholders:
            return (0, 0, 0)

        done = 0
        pending = 0
        failed = 0
        for hash_key in placeholders:
            status = self._plantuml_results.get(hash_key, ("pending", ""))[0]
            if status == "done":
                done += 1
            elif status == "error":
                failed += 1
            else:
                pending += 1
        return (done, pending, failed)

    def _show_preview_progress_status(self) -> None:
        """Publish a detailed current-file status while preview assets settle."""
        if self.current_file is None:
            self.statusBar().showMessage(self._default_status_text)
            return

        progress = self._preview_plantuml_progress()
        if progress is None:
            self.statusBar().showMessage(self._default_status_text)
            return

        done, pending, failed = progress
        if done == 0 and pending == 0 and failed == 0:
            self.statusBar().showMessage(f"Preview ready: {self.current_file.name}", 3500)
            return

        total = done + pending + failed
        if pending > 0:
            message = (
                f"Preview shown: {self.current_file.name} "
                f"(PlantUML {done}/{total} ready, {pending} rendering"
            )
            if failed > 0:
                message += f", {failed} failed"
            message += ")"
            self.statusBar().showMessage(message)
            return

        if failed > 0:
            self.statusBar().showMessage(
                f"Preview ready: {self.current_file.name} "
                f"(PlantUML {done}/{total} ready, {failed} failed)",
                5000,
            )
            return

        self.statusBar().showMessage(
            f"Preview ready: {self.current_file.name} (PlantUML {done}/{total} ready)",
            3500,
        )

    def _set_root_directory(self, new_root: Path) -> None:
        """Re-root the tree view and reset file preview state."""
        self._stop_restore_overlay_monitor()
        self._capture_current_preview_scroll(force=True)
        self._persist_document_view_session()
        self._capture_splitter_sizes_for_session()
        self.root = new_root.resolve()
        self.statusBar().showMessage(f"Root changed to {self.root}", 3000)
        self.last_directory_selection = self.root
        self.current_file = None
        self._current_document_total_lines = 1
        self._reset_document_views()
        self._clear_current_preview_signature()
        self._preview_capture_enabled = False
        self._scroll_restore_block_until = 0.0
        self._pending_preview_search_terms = []
        self._pending_preview_search_close_groups = []
        root_index = self.model.setRootPath(str(self.root))
        self.tree.setRootIndex(root_index)
        self.tree.clearSelection()
        self.path_label.setText("Select a markdown file")
        self._set_preview_html(
            self._placeholder_html("Select a markdown file to preview"),
            QUrl.fromLocalFile(f"{self.root}/"),
        )
        self._initial_split_applied = False
        self._update_up_button_state()
        self._update_window_title()
        self._cancel_pending_preview_render()
        self._rerun_active_search_for_scope()
        self._update_add_view_button_state()
        self._refresh_tree_multi_view_markers()
        QTimer.singleShot(0, self._maybe_apply_initial_split)

    def _on_preview_load_finished(self, ok: bool) -> None:
        """Apply deferred in-preview highlighting after a page finishes loading."""
        if not ok:
            self._stop_restore_overlay_monitor()
            self.statusBar().showMessage("Preview load failed", 5000)
            return
        current_key = self._current_preview_path_key()
        if current_key is None:
            self._stop_restore_overlay_monitor()
            return
        # Kick client-side renderer startup now and a bit later to tolerate
        # delayed external script availability (MathJax/Mermaid).
        self._trigger_client_renderers_for(current_key)
        QTimer.singleShot(450, lambda key=current_key: self._trigger_client_renderers_for(key))
        QTimer.singleShot(1500, lambda key=current_key: self._trigger_client_renderers_for(key))
        # PlantUML completions are patched in-place, but a full page load can
        # still happen from cache refreshes; re-apply any ready results.
        self._apply_all_ready_plantuml_to_current_preview()
        self._schedule_mermaid_cache_harvest_for(current_key)
        self._reapply_diagram_view_state_for(current_key)
        QTimer.singleShot(120, lambda key=current_key: self._reapply_diagram_view_state_for(key))
        QTimer.singleShot(420, lambda key=current_key: self._reapply_diagram_view_state_for(key))
        QTimer.singleShot(980, lambda key=current_key: self._reapply_diagram_view_state_for(key))
        has_saved_scroll = self._has_saved_scroll_for_current_preview()
        if self._pending_preview_search_terms:
            # Search normally scrolls to first hit. If this file has a saved
            # scroll position, preserve that location instead.
            self._highlight_preview_search_terms(
                self._pending_preview_search_terms,
                scroll_to_first=not has_saved_scroll,
                close_term_groups=self._pending_preview_search_close_groups,
            )
        if has_saved_scroll:
            # Re-apply a few times because late MathJax/Mermaid/layout work can
            # shift content after the initial load.
            self._preview_capture_enabled = False
            self._scroll_restore_block_until = time.monotonic() + 1.2
            QTimer.singleShot(90, lambda key=current_key: self._restore_current_preview_scroll(key))
            QTimer.singleShot(320, lambda key=current_key: self._restore_current_preview_scroll(key))
            QTimer.singleShot(900, lambda key=current_key: self._restore_current_preview_scroll(key))
            QTimer.singleShot(1250, lambda key=current_key: self._enable_preview_scroll_capture_for(key))
        else:
            self._preview_capture_enabled = True
            self._scroll_restore_block_until = 0.0
        self._request_active_view_top_line_update(force=True)
        self._show_preview_progress_status()
        self._check_restore_overlay_progress()

    def _trigger_client_renderers_for(self, expected_key: str) -> None:
        """Run in-page renderer helpers only if the same preview is still active."""
        if self._current_preview_path_key() != expected_key:
            return
        js = """
(() => {
  if (window.__mdexploreRunClientRenderers) {
    window.__mdexploreRunClientRenderers();
  } else if (window.__mdexploreTryTypesetMath) {
    window.__mdexploreTryTypesetMath();
  }
})();
"""
        self.preview.page().runJavaScript(js)

    def _update_up_button_state(self) -> None:
        self.up_btn.setEnabled(self.root.parent != self.root)

    def _go_up_directory(self) -> None:
        """Navigate one level up from the current root."""
        parent = self.root.parent
        if parent == self.root:
            return
        self._set_root_directory(parent)

    def _expanded_directory_paths(self) -> list[str]:
        """Capture currently expanded directory paths under the visible root."""
        root_index = self.tree.rootIndex()
        if not root_index.isValid():
            return []

        stack = [root_index]
        expanded_paths: list[str] = []
        seen: set[str] = set()

        while stack:
            index = stack.pop()
            if not index.isValid():
                continue

            path_text = self.model.filePath(index)
            path = Path(path_text)
            try:
                is_dir = path.is_dir()
            except Exception:
                is_dir = False
            if not is_dir:
                continue

            if self.tree.isExpanded(index):
                path_key = self._path_key(path)
                if path_key not in seen:
                    seen.add(path_key)
                    expanded_paths.append(path_key)

                # Ensure child indexes are available so nested expanded paths
                # can be captured/restored.
                if self.model.canFetchMore(index):
                    self.model.fetchMore(index)
                for row in range(self.model.rowCount(index)):
                    child_index = self.model.index(row, 0, index)
                    if child_index.isValid():
                        stack.append(child_index)

        return expanded_paths

    def _restore_expanded_directory_paths(self, paths: list[str]) -> None:
        """Restore expanded directories that still exist after a model refresh."""
        for path_text in paths:
            index = self.model.index(path_text)
            if index.isValid():
                self.tree.expand(index)

    def _refresh_directory_view(self, _checked: bool = False) -> None:
        """Refresh tree contents to detect newly created/deleted markdown files."""
        self._stop_restore_overlay_monitor()
        self.statusBar().showMessage("Refreshing directory view...")
        selected_path: Path | None = None
        current_index = self.tree.currentIndex()
        if current_index.isValid():
            try:
                selected_path = Path(self.model.filePath(current_index)).resolve()
            except Exception:
                selected_path = Path(self.model.filePath(current_index))

        expanded_paths = self._expanded_directory_paths()

        # Force QFileSystemModel to re-scan root by toggling root path.
        self.model.setRootPath("")
        root_index = self.model.setRootPath(str(self.root))
        self.tree.setRootIndex(root_index)
        self._refresh_tree_multi_view_markers()

        if expanded_paths:
            self._restore_expanded_directory_paths(expanded_paths)

        restored_selection = False
        if selected_path is not None:
            selected_index = self.model.index(str(selected_path))
            if selected_index.isValid():
                self.tree.setCurrentIndex(selected_index)
                restored_selection = True

        if self.current_file is not None:
            try:
                current_exists = self.current_file.is_file()
            except Exception:
                current_exists = False
            if not current_exists:
                self.current_file = None
                self._stop_restore_overlay_monitor()
                self._reset_document_views()
                self._clear_current_preview_signature()
                self.path_label.setText("Select a markdown file")
                self._set_preview_html(
                    self._placeholder_html("Select a markdown file to preview"),
                    QUrl.fromLocalFile(f"{self.root}/"),
                )
                if not restored_selection:
                    self.tree.clearSelection()
                self.statusBar().showMessage("Directory view refreshed; preview file no longer exists", 4500)
            else:
                self.statusBar().showMessage("Directory view refreshed", 2500)
        else:
            self.statusBar().showMessage("Directory view refreshed", 2500)

        self._update_window_title()
        self._update_up_button_state()
        self._update_add_view_button_state()
        self._rerun_active_search_for_scope()

    def _on_splitter_moved(self, _pos: int, _index: int) -> None:
        """Persist current pane split after any manual divider movement."""
        self._capture_splitter_sizes_for_session()

    def _capture_splitter_sizes_for_session(self) -> None:
        """Store non-zero splitter sizes for reuse while app stays open."""
        sizes = self.splitter.sizes()
        if len(sizes) != 2:
            return
        left_width = int(sizes[0])
        right_width = int(sizes[1])
        if left_width <= 0 or right_width <= 0:
            return
        self._session_splitter_sizes = [left_width, right_width]

    def _maybe_apply_initial_split(self, *_args) -> None:
        # Qt may override splitter sizes during initial layout/model load.
        # Re-apply either user-adjusted session split or initial 25/75 once
        # real geometry is known.
        if self._initial_split_applied:
            return
        total_width = max(self.splitter.width(), self.width())
        if total_width <= 0:
            return

        left_min = max(200, self.tree.minimumWidth())
        left_max = max(left_min, self.tree.maximumWidth())
        if self._session_splitter_sizes and len(self._session_splitter_sizes) == 2:
            previous_left, previous_right = self._session_splitter_sizes
            previous_total = max(1, int(previous_left) + int(previous_right))
            left_width = int(round(total_width * (int(previous_left) / previous_total)))
        else:
            left_width = total_width // 4

        left_width = max(left_min, min(left_max, left_width))
        right_width = max(400, total_width - left_width)
        left_width = max(left_min, min(left_max, total_width - right_width))
        self.splitter.setSizes([left_width, right_width])
        self._capture_splitter_sizes_for_session()
        self._initial_split_applied = True

    def _on_match_text_changed(self, text: str) -> None:
        """Debounce free-form match input before running a new search."""
        self._match_input_text = text
        self.match_clear_action.setVisible(bool(text.strip()))
        if not text.strip():
            self.match_timer.stop()
            self._clear_match_results()
            return
        self.match_timer.start()

    def _clear_match_input(self) -> None:
        """Clear search text and immediately remove any active match styling."""
        self.match_timer.stop()
        self.match_input.clear()
        self._clear_match_results()

    def _run_match_search_now(self) -> None:
        """Run search immediately, bypassing debounce delay."""
        self.match_timer.stop()
        self._run_match_search()

    def _cancel_pending_preview_render(self) -> None:
        """Drop queued preview render jobs and invalidate running results."""
        self._render_request_id += 1
        self._render_pool.clear()

    def _rerun_active_search_for_scope(self) -> None:
        """Re-run search immediately when scope changes and query is active."""
        if not self.match_input.text().strip():
            return
        self.match_timer.stop()
        self._run_match_search()

    def _clear_match_results(self) -> None:
        """Clear bolded search matches without affecting persisted highlights."""
        self.current_match_files = []
        self.model.clear_search_match_paths()
        self.tree.viewport().update()
        self._remove_preview_search_highlights()

    def _run_match_search(self) -> None:
        """Search current scope non-recursively and bold matching markdown files."""
        query = self.match_input.text().strip()
        if not query:
            self._clear_match_results()
            return

        scope = self._highlight_scope_directory()
        predicate = self._compile_match_predicate(query)
        candidates = self._list_markdown_files_non_recursive(scope)
        self.statusBar().showMessage(
            f"Searching {len(candidates)} markdown file(s) in {scope}...",
        )
        matches: list[Path] = []

        for path in candidates:
            try:
                content = path.read_text(encoding="utf-8", errors="replace")
            except Exception:
                content = ""
            # Search over file name + body to support quick discovery.
            if predicate(path.name, content):
                matches.append(path)

        self.current_match_files = matches
        self.model.set_search_match_paths(set(matches))
        self.tree.viewport().update()
        self.statusBar().showMessage(
            f"Matched {len(matches)} of {len(candidates)} markdown file(s) in {scope}",
            3500,
        )
        if self.current_file is not None:
            if self._is_path_in_current_matches(self.current_file):
                self._highlight_preview_search_terms(
                    self._current_search_terms(),
                    scroll_to_first=False,
                    close_term_groups=self._current_close_term_groups(),
                )
            else:
                self._remove_preview_search_highlights()

    @staticmethod
    def _path_key(path: Path) -> str:
        try:
            return str(path.resolve())
        except Exception:
            return str(path)

    def _is_path_in_current_matches(self, path: Path) -> bool:
        """Return whether a file path is in the latest search match set."""
        target = self._path_key(path)
        for candidate in self.current_match_files:
            if self._path_key(candidate) == target:
                return True
        return False

    @staticmethod
    def _session_has_multiple_views(session: dict | None) -> bool:
        """Return whether a persisted/in-memory session represents more than one view."""
        if not isinstance(session, dict):
            return False
        tabs = session.get("tabs")
        return isinstance(tabs, list) and len(tabs) > 1

    def _refresh_tree_multi_view_markers(self) -> None:
        """Update left-tree badges for markdown files that have multi-view state."""
        if not hasattr(self, "model"):
            return
        root = getattr(self, "root", None)
        if not isinstance(root, Path) or not root.exists():
            self.model.clear_multi_view_paths()
            if hasattr(self, "tree"):
                self.tree.viewport().update()
            return

        marked_paths: set[Path] = set()
        root_key = self._path_key(root)

        for raw_path_key, session in self._document_view_sessions.items():
            if not self._session_has_multiple_views(session):
                continue
            try:
                path = Path(raw_path_key).resolve()
            except Exception:
                path = Path(raw_path_key)
            path_key = self._path_key(path)
            if path_key == root_key or not path_key.startswith(root_key + os.sep):
                continue
            marked_paths.add(path)

        if self.current_file is not None and self.view_tabs.count() > 1:
            try:
                current_path = self.current_file.resolve()
            except Exception:
                current_path = self.current_file
            current_path_key = self._path_key(current_path)
            if current_path_key != root_key and current_path_key.startswith(root_key + os.sep):
                marked_paths.add(current_path)

        def on_walk_error(_err) -> None:
            return

        for dirpath, _dirnames, filenames in os.walk(root, onerror=on_walk_error, followlinks=False):
            if self.VIEWS_FILE_NAME not in filenames:
                continue
            directory = Path(dirpath)
            sessions = self._directory_view_sessions(directory)
            for file_name, session in sessions.items():
                if not self._session_has_multiple_views(session):
                    continue
                marked_paths.add(directory / file_name)

        self.model.set_multi_view_paths(marked_paths)
        if hasattr(self, "tree"):
            self.tree.viewport().update()

    def _current_search_terms(self) -> list[str]:
        """Extract searchable terms from the current query (operators excluded)."""
        query = self.match_input.text().strip()
        if not query:
            return []
        terms: list[str] = []
        seen: set[str] = set()
        for token_type, token_value, is_quoted in self._tokenize_match_query(query):
            if token_type != "TERM":
                continue
            term = token_value.strip()
            if not term:
                continue
            key = f"Q:{term}" if is_quoted else f"I:{term.casefold()}"
            if key in seen:
                continue
            seen.add(key)
            terms.append(term)
        terms.sort(key=len, reverse=True)
        return terms

    def _current_close_term_groups(self) -> list[list[tuple[str, bool]]]:
        """Extract CLOSE(...) argument groups from the current query."""
        query = self.match_input.text().strip()
        if not query:
            return []

        tokens = self._tokenize_match_query(query)
        groups: list[list[tuple[str, bool]]] = []
        i = 0
        token_count = len(tokens)

        while i < token_count:
            token_type, _token_value, _token_quoted = tokens[i]
            if token_type != "CLOSE":
                i += 1
                continue

            # Require function-style CLOSE (...) call shape.
            if i + 1 >= token_count or tokens[i + 1][0] != "LPAREN":
                i += 1
                continue

            j = i + 2
            group: list[tuple[str, bool]] = []
            is_valid = False

            while j < token_count:
                part_type, part_value, part_quoted = tokens[j]
                if part_type == "RPAREN":
                    is_valid = True
                    break
                if part_type == "COMMA":
                    j += 1
                    continue
                if part_type == "TERM":
                    cleaned = part_value.strip()
                    if cleaned:
                        group.append((cleaned, part_quoted))
                    j += 1
                    continue
                # Any nested expression token invalidates this CLOSE group.
                is_valid = False
                break

            if is_valid and len(group) >= 2:
                groups.append(group)
            i = j + 1 if j > i else i + 1

        return groups

    def _remove_preview_search_highlights(self) -> None:
        """Remove in-preview search highlight spans from the current page."""
        js = """
(() => {
  // Highlight spans are synthetic; remove them to restore original text nodes.
  const root = document.querySelector("main") || document.body;
  if (!root) return 0;
  const marks = root.querySelectorAll('span[data-mdexplore-search-mark="1"]');
  for (const mark of marks) {
    const parent = mark.parentNode;
    if (!parent) continue;
    parent.replaceChild(document.createTextNode(mark.textContent || ""), mark);
    parent.normalize();
  }
  return marks.length;
})();
"""
        # Mutates preview DOM to strip search marks; return value is not needed.
        self.preview.page().runJavaScript(js)

    def _highlight_preview_search_terms(
        self,
        terms: list[str],
        scroll_to_first: bool,
        close_term_groups: list[list[tuple[str, bool]]] | None = None,
    ) -> None:
        """Highlight term matches in preview and optionally scroll to first one."""
        cleaned_terms = [term.strip() for term in terms if term.strip()]
        if not cleaned_terms:
            self._remove_preview_search_highlights()
            return

        terms_json = json.dumps(cleaned_terms)
        scroll_json = "true" if scroll_to_first else "false"
        close_word_gap_json = str(int(SEARCH_CLOSE_WORD_GAP))
        close_groups_payload: list[list[dict[str, object]]] = []
        for group in close_term_groups or []:
            payload_group: list[dict[str, object]] = []
            for term_text, is_quoted in group:
                cleaned = term_text.strip()
                if cleaned:
                    payload_group.append({"text": cleaned, "quoted": bool(is_quoted)})
            if len(payload_group) >= 2:
                close_groups_payload.append(payload_group)
        close_groups_json = json.dumps(close_groups_payload)
        js = """
(() => {
  // Rebuild highlight spans from plain text each pass so updates are idempotent.
  const terms = __TERMS_JSON__;
  const shouldScroll = __SCROLL_BOOL__;
  const closeWordGap = __CLOSE_WORD_GAP__;
  const closeTermGroups = __CLOSE_GROUPS_JSON__;
  const root = document.querySelector("main") || document.body;
  if (!root || !terms.length) return 0;

  const markSelector = 'span[data-mdexplore-search-mark="1"]';
  for (const oldMark of root.querySelectorAll(markSelector)) {
    const parent = oldMark.parentNode;
    if (!parent) continue;
    parent.replaceChild(document.createTextNode(oldMark.textContent || ""), oldMark);
    parent.normalize();
  }

  const skipTags = new Set(["SCRIPT", "STYLE", "NOSCRIPT", "TEXTAREA"]);
  const walker = document.createTreeWalker(
    root,
    NodeFilter.SHOW_TEXT,
    {
      acceptNode(node) {
        if (!node || !node.nodeValue || !node.nodeValue.trim()) {
          return NodeFilter.FILTER_REJECT;
        }
        const parent = node.parentElement;
        if (!parent) {
          return NodeFilter.FILTER_REJECT;
        }
        if (skipTags.has(parent.tagName)) {
          return NodeFilter.FILTER_REJECT;
        }
        if (parent.closest(markSelector)) {
          return NodeFilter.FILTER_REJECT;
        }
        return NodeFilter.FILTER_ACCEPT;
      },
    },
  );

  const segments = [];
  let fullText = "";
  while (walker.nextNode()) {
    const node = walker.currentNode;
    const value = node.nodeValue || "";
    if (!value) {
      continue;
    }
    const start = fullText.length;
    fullText += value;
    const end = fullText.length;
    segments.push({ node, text: value, start, end });
    // Separate nodes to avoid accidental cross-node token merging.
    fullText += "\\n";
  }
  if (!segments.length) return 0;

  function escapeRegExp(input) {
    return String(input || "").replace(/[.*+?^${}()|[\\]\\\\]/g, "\\\\$&");
  }

  function upperBound(values, target) {
    let lo = 0;
    let hi = values.length;
    while (lo < hi) {
      const mid = (lo + hi) >> 1;
      if (values[mid] <= target) {
        lo = mid + 1;
      } else {
        hi = mid;
      }
    }
    return lo;
  }

  function normalizeCloseGroups(groups) {
    if (!Array.isArray(groups)) return [];
    const normalized = [];
    for (const group of groups) {
      if (!Array.isArray(group)) continue;
      const next = [];
      for (const item of group) {
        if (!item || typeof item.text !== "string") continue;
        const text = item.text.trim();
        if (!text) continue;
        next.push({ text, quoted: !!item.quoted });
      }
      if (next.length >= 2) normalized.push(next);
    }
    return normalized;
  }

  const normalizedCloseGroups = normalizeCloseGroups(closeTermGroups);
  let closeFocusRange = null;
  let closeFocusTerms = null;

  if (normalizedCloseGroups.length) {
    const wordMatches = [];
    const wordRegex = /\\S+/g;
    let wordMatch = null;
    while ((wordMatch = wordRegex.exec(fullText)) !== null) {
      wordMatches.push({ start: wordMatch.index, end: wordMatch.index + wordMatch[0].length });
      if (wordRegex.lastIndex <= wordMatch.index) {
        wordRegex.lastIndex = wordMatch.index + 1;
      }
    }

    if (wordMatches.length) {
      const wordStarts = wordMatches.map((item) => item.start);

      function bestWindowForGroup(group) {
        const occurrences = [];
        const found = new Array(group.length).fill(false);

        for (let termIndex = 0; termIndex < group.length; termIndex += 1) {
          const termInfo = group[termIndex];
          const pattern = new RegExp(escapeRegExp(termInfo.text), termInfo.quoted ? "g" : "gi");
          let m = null;
          while ((m = pattern.exec(fullText)) !== null) {
            const startChar = m.index;
            const wordIndex = upperBound(wordStarts, startChar) - 1;
            if (wordIndex >= 0) {
              occurrences.push({ word: wordIndex, term: termIndex });
              found[termIndex] = true;
            }
            if (pattern.lastIndex <= startChar) {
              pattern.lastIndex = startChar + 1;
            }
          }
        }

        if (!occurrences.length || found.some((value) => !value)) {
          return null;
        }

        occurrences.sort((a, b) => a.word - b.word);
        const counts = new Array(group.length).fill(0);
        let have = 0;
        let left = 0;
        let best = null;

        for (let right = 0; right < occurrences.length; right += 1) {
          const rightOcc = occurrences[right];
          if (counts[rightOcc.term] === 0) {
            have += 1;
          }
          counts[rightOcc.term] += 1;

          while (have === group.length && left <= right) {
            const leftOcc = occurrences[left];
            const span = rightOcc.word - leftOcc.word;
            if (span <= closeWordGap) {
              if (!best || span < best.span || (span === best.span && leftOcc.word < best.leftWord)) {
                best = { span, leftWord: leftOcc.word, rightWord: rightOcc.word };
              }
            }
            counts[leftOcc.term] -= 1;
            if (counts[leftOcc.term] === 0) {
              have -= 1;
            }
            left += 1;
          }
        }

        if (!best) {
          return null;
        }
        const startWord = wordMatches[best.leftWord];
        const endWord = wordMatches[best.rightWord];
        if (!startWord || !endWord) {
          return null;
        }
        return {
          span: best.span,
          startChar: startWord.start,
          endChar: endWord.end,
          terms: group,
        };
      }

      let chosenWindow = null;
      for (const group of normalizedCloseGroups) {
        const candidate = bestWindowForGroup(group);
        if (!candidate) continue;
        if (!chosenWindow || candidate.span < chosenWindow.span || (candidate.span === chosenWindow.span && candidate.startChar < chosenWindow.startChar)) {
          chosenWindow = candidate;
        }
      }

      if (chosenWindow) {
        closeFocusRange = { startChar: chosenWindow.startChar, endChar: chosenWindow.endChar };
        closeFocusTerms = chosenWindow.terms;
      }
    }
  }

  // If CLOSE(...) is present, only highlight the matched CLOSE window.
  if (normalizedCloseGroups.length && !closeFocusRange) {
    return 0;
  }

  const targetTerms = closeFocusTerms || terms.map((text) => ({ text, quoted: false }));
  if (!targetTerms.length) return 0;

  function collectRanges(segment) {
    const ranges = [];
    for (const termInfo of targetTerms) {
      const rawText = termInfo && typeof termInfo.text === "string" ? termInfo.text : "";
      const termText = rawText.trim();
      if (!termText) continue;
      const pattern = new RegExp(escapeRegExp(termText), termInfo.quoted ? "g" : "gi");
      let m = null;
      while ((m = pattern.exec(segment.text)) !== null) {
        const localStart = m.index;
        const localEnd = localStart + m[0].length;
        const absoluteStart = segment.start + localStart;
        const absoluteEnd = segment.start + localEnd;
        if (closeFocusRange) {
          if (absoluteStart < closeFocusRange.startChar || absoluteEnd > closeFocusRange.endChar) {
            if (pattern.lastIndex <= localStart) {
              pattern.lastIndex = localStart + 1;
            }
            continue;
          }
        }
        ranges.push({ start: localStart, end: localEnd });
        if (pattern.lastIndex <= localStart) {
          pattern.lastIndex = localStart + 1;
        }
      }
    }

    if (!ranges.length) {
      return [];
    }

    ranges.sort((a, b) => {
      if (a.start !== b.start) return a.start - b.start;
      return (b.end - b.start) - (a.end - a.start);
    });

    const deduped = [];
    let lastEnd = -1;
    for (const item of ranges) {
      if (item.start < lastEnd) continue;
      deduped.push(item);
      lastEnd = item.end;
    }
    return deduped;
  }

  let firstMark = null;
  let matchCount = 0;
  for (const segment of segments) {
    const ranges = collectRanges(segment);
    if (!ranges.length) continue;

    const text = segment.text;
    let cursor = 0;
    const fragment = document.createDocumentFragment();
    for (const range of ranges) {
      if (range.start > cursor) {
        fragment.appendChild(document.createTextNode(text.slice(cursor, range.start)));
      }
      const mark = document.createElement("span");
      mark.setAttribute("data-mdexplore-search-mark", "1");
      mark.style.backgroundColor = "#f5d34f";
      mark.style.color = "#111827";
      mark.style.padding = "0 1px";
      mark.style.borderRadius = "2px";
      mark.textContent = text.slice(range.start, range.end);
      fragment.appendChild(mark);
      if (!firstMark) {
        firstMark = mark;
      }
      matchCount += 1;
      cursor = range.end;
    }
    if (cursor < text.length) {
      fragment.appendChild(document.createTextNode(text.slice(cursor)));
    }
    const parent = segment.node.parentNode;
    if (parent) {
      parent.replaceChild(fragment, segment.node);
    }
  }

  if (firstMark && shouldScroll) {
    firstMark.scrollIntoView({ behavior: "auto", block: "center", inline: "nearest" });
  }
  return matchCount;
})();
"""
        js = js.replace("__TERMS_JSON__", terms_json)
        js = js.replace("__SCROLL_BOOL__", scroll_json)
        js = js.replace("__CLOSE_WORD_GAP__", close_word_gap_json)
        js = js.replace("__CLOSE_GROUPS_JSON__", close_groups_json)
        # Mutates preview DOM by inserting mark spans (and optional scroll).
        self.preview.page().runJavaScript(js)

    def _list_markdown_files_non_recursive(self, directory: Path) -> list[Path]:
        """Return direct child markdown files from a directory (non-recursive)."""
        if not directory.is_dir():
            return []

        try:
            entries = sorted(directory.iterdir(), key=lambda item: item.name.casefold())
        except Exception:
            return []

        files: list[Path] = []
        for entry in entries:
            try:
                if entry.is_file() and entry.suffix.lower() == ".md":
                    files.append(entry.resolve())
            except Exception:
                # Ignore files that disappear or become inaccessible mid-scan.
                pass
        return files

    def _compile_match_predicate(self, query: str):
        """Compile boolean query with implicit AND, quotes, and CLOSE(...)."""
        tokens = self._tokenize_match_query(query)
        if not tokens:
            return lambda _name, _content: True

        class QueryParseError(Exception):
            pass

        idx = 0

        def peek(offset: int = 0) -> tuple[str, str, bool] | None:
            token_index = idx + offset
            if 0 <= token_index < len(tokens):
                return tokens[token_index]
            return None

        def token_starts_expression(token_index: int) -> bool:
            if token_index < 0 or token_index >= len(tokens):
                return False
            token_type, token_value, _token_quoted = tokens[token_index]
            if token_type in {"TERM", "LPAREN", "CLOSE"}:
                return True
            if token_type == "OP" and token_value == "NOT":
                return True
            if token_type == "OP" and token_value in {"AND", "OR"}:
                next_token = tokens[token_index + 1] if token_index + 1 < len(tokens) else None
                return bool(next_token and next_token[0] == "LPAREN")
            return False

        def consume(expected_type: str | None = None, expected_value: str | None = None) -> tuple[str, str, bool]:
            nonlocal idx
            token = peek()
            if token is None:
                raise QueryParseError("Unexpected end of query")
            token_type, token_value, token_quoted = token
            if expected_type is not None and token_type != expected_type:
                raise QueryParseError(f"Expected {expected_type} but found {token_type}")
            if expected_value is not None and token_value != expected_value:
                raise QueryParseError(f"Expected {expected_value} but found {token_value}")
            idx += 1
            return token_type, token_value, token_quoted

        def parse_expression(allow_implicit_and: bool = True):
            return parse_or(allow_implicit_and)

        def parse_or(allow_implicit_and: bool = True):
            node = parse_and(allow_implicit_and)
            while True:
                token = peek()
                if token is None or token[0] != "OP" or token[1] != "OR":
                    break
                consume("OP", "OR")
                right = parse_and(allow_implicit_and)
                node = ("OR", node, right)
            return node

        def parse_and(allow_implicit_and: bool = True):
            node = parse_not(allow_implicit_and)
            while True:
                token = peek()
                if token is not None and token[0] == "OP" and token[1] == "AND":
                    consume("OP", "AND")
                    right = parse_not(allow_implicit_and)
                    node = ("AND", node, right)
                    continue
                # Implicit AND between adjacent expressions.
                if allow_implicit_and and token_starts_expression(idx):
                    right = parse_not(allow_implicit_and)
                    node = ("AND", node, right)
                    continue
                break
            return node

        def parse_not(allow_implicit_and: bool = True):
            token = peek()
            if token is not None and token[0] == "OP" and token[1] == "NOT":
                consume("OP", "NOT")
                return ("NOT", parse_not(allow_implicit_and))
            return parse_primary(allow_implicit_and)

        def parse_logic_call(operator_name: str):
            consume("OP", operator_name)
            consume("LPAREN")
            while True:
                token = peek()
                if token is None:
                    raise QueryParseError(f"Unterminated {operator_name}(...)")
                if token[0] == "RPAREN":
                    break
                if token[0] == "COMMA":
                    consume("COMMA")
                    continue
                if not token_starts_expression(idx):
                    raise QueryParseError(f"{operator_name}() accepts expression arguments only")
                break

            items: list[tuple] = []
            while True:
                token = peek()
                if token is None:
                    raise QueryParseError(f"Unterminated {operator_name}(...)")
                if token[0] == "RPAREN":
                    break
                if token[0] == "COMMA":
                    consume("COMMA")
                    continue

                # Function-style args accept comma, whitespace, or a mix.
                items.append(parse_expression(allow_implicit_and=False))
                token = peek()
                if token is None:
                    raise QueryParseError(f"Unterminated {operator_name}(...)")
                if token[0] == "COMMA":
                    consume("COMMA")
                    continue
                if token[0] == "RPAREN":
                    break
                if token_starts_expression(idx):
                    continue
                raise QueryParseError(f"Unexpected token in {operator_name}(...)")

            consume("RPAREN")
            if not items:
                raise QueryParseError(f"{operator_name}() requires at least one argument")
            combined = items[0]
            for item in items[1:]:
                combined = (operator_name, combined, item)
            return combined

        def parse_close_call():
            consume("CLOSE", "CLOSE")
            consume("LPAREN")
            terms: list[tuple[str, bool]] = []
            while True:
                token = peek()
                if token is None:
                    raise QueryParseError("Unterminated CLOSE(...)")
                token_type, token_value, token_quoted = token
                if token_type == "RPAREN":
                    break
                if token_type == "COMMA":
                    consume("COMMA")
                    continue
                if token_type == "TERM":
                    consume("TERM")
                    cleaned = token_value.strip()
                    if cleaned:
                        terms.append((cleaned, token_quoted))
                    continue
                raise QueryParseError("CLOSE(...) accepts terms only")
            consume("RPAREN")
            if len(terms) < 2:
                raise QueryParseError("CLOSE(...) requires at least two terms")
            return ("CLOSE", terms)

        def parse_primary(_allow_implicit_and: bool = True):
            token = peek()
            if token is None:
                raise QueryParseError("Missing query operand")
            token_type, token_value, token_quoted = token
            if token_type == "TERM":
                consume("TERM")
                return ("TERM", token_value, token_quoted)
            if token_type == "CLOSE":
                return parse_close_call()
            if token_type == "OP" and token_value in {"AND", "OR"} and peek(1) is not None and peek(1)[0] == "LPAREN":
                return parse_logic_call(token_value)
            if token_type == "LPAREN":
                consume("LPAREN")
                node = parse_expression()
                consume("RPAREN")
                return node
            raise QueryParseError(f"Unexpected token: {token_type}")

        def term_matches(
            term: str,
            is_quoted: bool,
            file_name: str,
            file_content: str,
            file_name_folded: str,
            file_content_folded: str,
        ) -> bool:
            if not term:
                return False
            if is_quoted:
                return term in file_name or term in file_content
            term_folded = term.casefold()
            return term_folded in file_name_folded or term_folded in file_content_folded

        def close_terms_match(terms: list[tuple[str, bool]], file_content: str) -> bool:
            content = file_content or ""
            word_matches = list(re.finditer(r"\S+", content))
            if not word_matches:
                return False
            # CLOSE() uses whitespace-delimited token positions, not line indexes.
            word_starts = [match.start() for match in word_matches]
            content_folded = content.casefold()
            occurrences: list[tuple[int, int]] = []
            term_found = [False] * len(terms)

            for term_index, (term_text, is_quoted) in enumerate(terms):
                if not term_text:
                    return False
                needle = term_text if is_quoted else term_text.casefold()
                haystack = content if is_quoted else content_folded
                search_start = 0
                while True:
                    char_index = haystack.find(needle, search_start)
                    if char_index < 0:
                        break
                    word_index = bisect_right(word_starts, char_index) - 1
                    if word_index >= 0:
                        occurrences.append((word_index, term_index))
                        term_found[term_index] = True
                    search_start = char_index + 1

            if not all(term_found) or not occurrences:
                return False

            occurrences.sort(key=lambda item: item[0])
            counts = [0] * len(terms)
            have = 0
            left = 0

            for right, (right_word, right_term_index) in enumerate(occurrences):
                if counts[right_term_index] == 0:
                    have += 1
                counts[right_term_index] += 1

                while have == len(terms) and left <= right:
                    left_word, left_term_index = occurrences[left]
                    if right_word - left_word <= SEARCH_CLOSE_WORD_GAP:
                        return True
                    counts[left_term_index] -= 1
                    if counts[left_term_index] == 0:
                        have -= 1
                    left += 1

            return False

        def evaluate(node, file_name: str, file_content: str, file_name_folded: str, file_content_folded: str) -> bool:
            node_type = node[0]
            if node_type == "TERM":
                _kind, term_text, is_quoted = node
                return term_matches(term_text, bool(is_quoted), file_name, file_content, file_name_folded, file_content_folded)
            if node_type == "CLOSE":
                _kind, close_terms = node
                return close_terms_match(close_terms, file_content)
            if node_type == "NOT":
                _kind, operand = node
                return not evaluate(operand, file_name, file_content, file_name_folded, file_content_folded)
            if node_type == "AND":
                _kind, left_node, right_node = node
                return evaluate(left_node, file_name, file_content, file_name_folded, file_content_folded) and evaluate(
                    right_node,
                    file_name,
                    file_content,
                    file_name_folded,
                    file_content_folded,
                )
            if node_type == "OR":
                _kind, left_node, right_node = node
                return evaluate(left_node, file_name, file_content, file_name_folded, file_content_folded) or evaluate(
                    right_node,
                    file_name,
                    file_content,
                    file_name_folded,
                    file_content_folded,
                )
            return False

        try:
            expression = parse_expression()
            if idx != len(tokens):
                raise QueryParseError("Unexpected trailing query tokens")
        except QueryParseError:
            return self._compile_simple_match_predicate(tokens)

        def predicate(file_name: str, file_content: str) -> bool:
            name_text = file_name or ""
            content_text = file_content or ""
            return evaluate(
                expression,
                name_text,
                content_text,
                name_text.casefold(),
                content_text.casefold(),
            )

        return predicate

    def _compile_simple_match_predicate(self, tokens: list[tuple[str, str, bool]]):
        """Fallback matcher: all terms must appear in filename or content."""
        terms = [(value.strip(), is_quoted) for token_type, value, is_quoted in tokens if token_type == "TERM" and value.strip()]
        if not terms:
            return lambda _file_name, _file_content: True

        def predicate(file_name: str, file_content: str) -> bool:
            name_text = file_name or ""
            content_text = file_content or ""
            name_folded = name_text.casefold()
            content_folded = content_text.casefold()
            for term_text, is_quoted in terms:
                if is_quoted:
                    if term_text not in name_text and term_text not in content_text:
                        return False
                else:
                    folded = term_text.casefold()
                    if folded not in name_folded and folded not in content_folded:
                        return False
            return True

        return predicate

    def _tokenize_match_query(self, query: str) -> list[tuple[str, str, bool]]:
        """Tokenize query supporting AND/OR/NOT, CLOSE(...), quotes, and commas."""
        tokens: list[tuple[str, str, bool]] = []
        i = 0
        length = len(query)

        while i < length:
            ch = query[i]
            if ch.isspace():
                i += 1
                continue
            if ch == "(":
                tokens.append(("LPAREN", ch, False))
                i += 1
                continue
            if ch == ")":
                tokens.append(("RPAREN", ch, False))
                i += 1
                continue
            if ch == ",":
                tokens.append(("COMMA", ch, False))
                i += 1
                continue
            if ch == '"':
                i += 1
                buffer: list[str] = []
                while i < length:
                    current = query[i]
                    if current == "\\" and i + 1 < length:
                        next_char = query[i + 1]
                        if next_char in {'"', "\\"}:
                            buffer.append(next_char)
                            i += 2
                            continue
                    if current == '"':
                        i += 1
                        break
                    buffer.append(current)
                    i += 1
                tokens.append(("TERM", "".join(buffer), True))
                continue

            start = i
            while i < length and not query[i].isspace() and query[i] not in "(),":
                i += 1
            token_value = query[start:i]
            if not token_value:
                continue
            upper = token_value.upper()
            if upper in {"AND", "OR", "NOT"}:
                tokens.append(("OP", upper, False))
            elif upper == "CLOSE":
                tokens.append(("CLOSE", "CLOSE", False))
            else:
                tokens.append(("TERM", token_value, False))

        return tokens

    def _apply_match_highlight_color(self, color_value: str, color_name: str) -> None:
        """Apply a highlight color to current match set, then clear bolding."""
        self.match_timer.stop()
        if self.match_input.text().strip():
            self._run_match_search()

        if not self.current_match_files:
            self.statusBar().showMessage("No matched files to highlight", 3000)
            return

        updated = 0
        for path in self.current_match_files:
            try:
                if path.is_file() and path.suffix.lower() == ".md":
                    self.model.set_color_for_file(path, color_value)
                    updated += 1
            except Exception:
                # Ignore files that are no longer available.
                pass

        self._clear_match_results()
        self.statusBar().showMessage(
            f"Applied {color_name.lower()} highlight to {updated} matched file(s)",
            4000,
        )

    def _show_tree_context_menu(self, pos) -> None:
        """Show right-click menu for assigning a file highlight color."""
        index = self.tree.indexAt(pos)
        if not index.isValid():
            return
        self.tree.setCurrentIndex(index)
        self._update_window_title()
        path = Path(self.model.filePath(index))

        menu = QMenu(self)
        color_actions: dict[QAction, str] = {}
        clear_action: QAction | None = None

        if path.is_file() and path.suffix.lower() == ".md":
            for idx, (color_name, color_value) in enumerate(self.HIGHLIGHT_COLORS):
                label = f"Highlight {color_name}" if idx == 0 else f"... {color_name}"
                action = menu.addAction(label)
                action.setData(color_value)
                color_actions[action] = color_value

            menu.addSeparator()
            clear_action = menu.addAction("Clear Highlight")

        clear_all_action = menu.addAction("Clear All")
        chosen = menu.exec(self.tree.viewport().mapToGlobal(pos))
        if chosen is None:
            return
        if chosen == clear_all_action:
            self._confirm_and_clear_all_highlighting()
            self.tree.viewport().update()
            return

        if clear_action is not None and chosen == clear_action:
            self.model.set_color_for_file(path, None)
        elif chosen in color_actions:
            self.model.set_color_for_file(path, color_actions[chosen])
        self.tree.viewport().update()

    def _on_tree_directory_expanded(self, index) -> None:
        """Treat expanded directories as active scope for quit persistence/title."""
        if not index.isValid():
            return
        path = Path(self.model.filePath(index))
        if not path.is_dir():
            return
        was_selected = self.tree.currentIndex() == index
        self.tree.setCurrentIndex(index)
        self.last_directory_selection = path.resolve()
        self._update_window_title()
        if was_selected:
            self._rerun_active_search_for_scope()

    def _show_preview_context_menu(self, pos) -> None:
        """Extend the preview context menu with a markdown copy action."""
        request = self.preview.lastContextMenuRequest()
        selected_text_hint = request.selectedText() if request is not None else ""
        click_x = int(pos.x())
        click_y = int(pos.y())

        # Capture selection mapping before context-menu interaction to avoid
        # losing selection state when the menu action is triggered.
        js = """
(() => {
  const sel = window.getSelection();

  function lineInfo(node) {
    if (!node) return null;
    if (node.nodeType === Node.TEXT_NODE) node = node.parentElement;
    if (!(node instanceof Element)) return null;
    const el = node.closest('[data-md-line-start][data-md-line-end]');
    if (!el) return null;
    const start = parseInt(el.getAttribute('data-md-line-start'), 10);
    const end = parseInt(el.getAttribute('data-md-line-end'), 10);
    if (Number.isNaN(start) || Number.isNaN(end)) return null;
    return { start, end };
  }

  function normalizeRange(startInfo, endInfo) {
    let start = startInfo ? startInfo.start : endInfo.start;
    let end = endInfo ? endInfo.end : startInfo.end;
    if (start > end) {
      const tmp = start;
      start = end;
      end = tmp;
    }
    if (end <= start) end = start + 1;
    return { start, end };
  }

  function collectIntersectingRange(range) {
    if (!(range instanceof Range)) return null;
    let root = range.commonAncestorContainer;
    if (root && root.nodeType === Node.TEXT_NODE) root = root.parentElement;
    const scope =
      root instanceof Element
        ? root
        : (document.body || document.documentElement || document);
    const tagged = scope.querySelectorAll
      ? scope.querySelectorAll('[data-md-line-start][data-md-line-end]')
      : document.querySelectorAll('[data-md-line-start][data-md-line-end]');
    let minStart = null;
    let maxEnd = null;
    for (const el of tagged) {
      try {
        if (!range.intersectsNode(el)) continue;
      } catch (_err) {
        continue;
      }
      const start = parseInt(el.getAttribute('data-md-line-start') || '', 10);
      const end = parseInt(el.getAttribute('data-md-line-end') || '', 10);
      if (Number.isNaN(start) || Number.isNaN(end)) continue;
      minStart = minStart === null ? start : Math.min(minStart, start);
      maxEnd = maxEnd === null ? end : Math.max(maxEnd, end);
    }
    if (minStart === null || maxEnd === null) return null;
    return { start: minStart, end: Math.max(minStart + 1, maxEnd) };
  }

  const hasSelection = !!(sel && sel.toString && sel.toString().trim());
  const selectedText = hasSelection ? sel.toString() : "";
  // Preferred path: map the active text selection to source line metadata.
  if (sel && sel.rangeCount > 0 && !sel.isCollapsed) {
    const range = sel.getRangeAt(0);
    const intersecting = collectIntersectingRange(range);
    if (intersecting) {
      return { hasSelection: true, selectedText, ...intersecting, via: "selection-intersects" };
    }
    const startInfo = lineInfo(range.startContainer);
    const endInfo = lineInfo(range.endContainer);
    if (startInfo || endInfo) {
      return { hasSelection: true, selectedText, ...normalizeRange(startInfo, endInfo), via: "selection" };
    }
  }

  // Fallback: map from right-clicked block location.
  const clicked = document.elementFromPoint(__CLICK_X__, __CLICK_Y__);
  const clickedInfo = lineInfo(clicked);
  if (clickedInfo) {
    return {
      hasSelection,
      selectedText,
      start: clickedInfo.start,
      end: clickedInfo.end,
      via: "click",
    };
  }

  return { hasSelection, selectedText };
})();
"""
        js = js.replace("__CLICK_X__", str(click_x)).replace("__CLICK_Y__", str(click_y))
        # Returns selection + line-range metadata used to build copy actions.
        self.preview.page().runJavaScript(
            js,
            lambda result: self._show_preview_context_menu_with_cached_selection(pos, result, selected_text_hint),
        )

    def _show_preview_context_menu_with_cached_selection(self, pos, selection_info, selected_text_hint: str) -> None:
        """Build preview menu and use cached selection metadata for copy action."""
        menu = self.preview.createStandardContextMenu()
        has_selection = bool(selected_text_hint.strip() or self.preview.selectedText().strip())
        if isinstance(selection_info, dict) and selection_info.get("hasSelection"):
            has_selection = True

        copy_source_action: QAction | None = None
        copy_rendered_action: QAction | None = None
        if has_selection:
            menu.addSeparator()
            copy_rendered_action = menu.addAction("Copy Rendered Text")
            copy_source_action = menu.addAction("Copy Source Markdown")

        chosen = menu.exec(self.preview.mapToGlobal(pos))
        if copy_rendered_action is not None and chosen == copy_rendered_action:
            self._copy_preview_selection_as_rendered_text(selection_info, selected_text_hint)
            menu.deleteLater()
            return
        if copy_source_action is not None and chosen == copy_source_action:
            self._copy_preview_selection_as_source_markdown(selection_info, selected_text_hint)
        menu.deleteLater()

    def _copy_preview_selection_as_rendered_text(self, selection_info, selected_text_hint: str) -> None:
        """Copy currently selected rendered preview text as plain text."""
        selected_text = ""
        if isinstance(selection_info, dict):
            selected_raw = selection_info.get("selectedText")
            if isinstance(selected_raw, str):
                selected_text = selected_raw
        if not selected_text.strip():
            selected_text = selected_text_hint
        if not selected_text.strip():
            selected_text = self.preview.selectedText()
        if not selected_text.strip():
            self.statusBar().showMessage("No selected rendered text to copy", 3000)
            return

        self._set_plain_text_clipboard(selected_text)
        self.statusBar().showMessage("Copied rendered text", 3000)

    def _copy_preview_selection_as_source_markdown(self, selection_info, selected_text_hint: str) -> None:
        """Copy source markdown lines that correspond to selected preview content."""
        if self.current_file is None:
            self.statusBar().showMessage("No markdown file selected", 3000)
            return
        source_path = self.current_file
        try:
            lines = source_path.read_text(encoding="utf-8", errors="replace").splitlines(keepends=True)
        except Exception:
            self.statusBar().showMessage("Could not read source markdown file", 3000)
            return

        if not lines:
            QApplication.clipboard().setText("")
            self.statusBar().showMessage("Copied source markdown (empty file)", 3000)
            return

        if isinstance(selection_info, dict):
            start_raw = selection_info.get("start")
            end_raw = selection_info.get("end")
            if isinstance(start_raw, (int, float)) and isinstance(end_raw, (int, float)):
                start = max(0, int(start_raw))
                end = max(start + 1, int(end_raw))
                start = min(start, len(lines) - 1)
                end = min(end, len(lines))
                snippet = "".join(lines[start:end])
                self._set_plain_text_clipboard(snippet)
                self.statusBar().showMessage(
                    f"Copied source markdown lines {start + 1}-{end}",
                    3500,
                )
                return

        # Fallback: find selected text in source and copy containing source lines.
        js_selected_text = ""
        if isinstance(selection_info, dict):
            selected_raw = selection_info.get("selectedText")
            if isinstance(selected_raw, str):
                js_selected_text = selected_raw.strip()

        query = js_selected_text or selected_text_hint.strip() or self.preview.selectedText().strip()
        if not query:
            query = QApplication.clipboard().text(QClipboard.Mode.Clipboard).strip()
        if query:
            source_text = "".join(lines)
            found_at = source_text.find(query)
            if found_at != -1:
                line_start = source_text.count("\n", 0, found_at)
                line_end = source_text.count("\n", 0, found_at + len(query)) + 1
                line_start = min(line_start, len(lines) - 1)
                line_end = min(max(line_end, line_start + 1), len(lines))
                snippet = "".join(lines[line_start:line_end])
                self._set_plain_text_clipboard(snippet)
                self.statusBar().showMessage(
                    f"Copied source markdown lines {line_start + 1}-{line_end} (fallback)",
                    4000,
                )
                return

            normalized_match = self._find_source_span_by_normalized_document_match(lines, query)
            if normalized_match is not None:
                start_idx, end_idx, label = normalized_match
                snippet = "".join(lines[start_idx:end_idx])
                self._set_plain_text_clipboard(snippet)
                self.statusBar().showMessage(
                    f"Copied source markdown lines {start_idx + 1}-{end_idx} ({label})",
                    4000,
                )
                return

            fuzzy_match = self._find_source_span_by_fuzzy_lines(lines, query)
            if fuzzy_match is not None:
                start_idx, end_idx = fuzzy_match
                snippet = "".join(lines[start_idx:end_idx])
                self._set_plain_text_clipboard(snippet)
                self.statusBar().showMessage(
                    f"Copied source markdown lines {start_idx + 1}-{end_idx} (fuzzy)",
                    4000,
                )
                return

        self._set_plain_text_clipboard("".join(lines))
        self.statusBar().showMessage(
            "Could not map selection exactly; copied full source markdown",
            4500,
        )

    @staticmethod
    def _normalize_for_fuzzy_match(text: str) -> str:
        lowered = (
            text.casefold()
            .replace("\\", " ")
            .replace("—", " ")
            .replace("–", " ")
            .replace("\u00a0", " ")
        )
        stripped = re.sub(r"[`*_~>#\[\](){}|!+\-:;,.?/]", " ", lowered)
        stripped = re.sub(r"^\s*[-*+]\s+", "", stripped, flags=re.MULTILINE)
        stripped = re.sub(r"^\s*\d+[.)]\s+", "", stripped, flags=re.MULTILINE)
        return re.sub(r"\s+", " ", stripped).strip()

    @classmethod
    def _meaningful_normalized_query_lines(cls, query_text: str) -> list[str]:
        """Return non-empty normalized query lines for boundary refinement."""
        normalized: list[str] = []
        for raw_line in query_text.splitlines():
            value = cls._normalize_for_fuzzy_match(raw_line)
            if value:
                normalized.append(value)
        return normalized

    @staticmethod
    def _line_match_score(query_norm: str, candidate: str) -> float:
        """Score how well a normalized query line matches a normalized source line."""
        if not query_norm or not candidate:
            return 0.0
        if query_norm in candidate:
            return 0.92 + min(0.08, len(query_norm) / max(len(candidate), 1))
        if candidate in query_norm and len(candidate) >= 8:
            return 0.65 + min(0.20, len(candidate) / max(len(query_norm), 1))
        return SequenceMatcher(None, query_norm, candidate).ratio()

    @classmethod
    def _align_query_lines_to_source(
        cls,
        query_lines: list[str],
        normalized_lines: list[str],
        approx_start: int,
        approx_end: int,
    ) -> tuple[int, int] | None:
        """Refine an approximate source span by matching query lines in order."""
        if not query_lines:
            return None

        total_query_chars = sum(len(line) for line in query_lines)
        if total_query_chars < 32:
            return None

        search_start = max(0, approx_start - 18)
        search_end = min(
            len(normalized_lines),
            max(approx_end + max(48, len(query_lines) * 3), search_start + 1),
        )
        current_index = search_start
        matched_indexes: list[int] = []
        matched_chars = 0

        for query_norm in query_lines:
            if len(query_norm) < 3:
                continue

            best_idx = -1
            best_score = 0.0
            line_span_end = min(search_end, current_index + max(42, len(query_lines) * 2))
            for idx in range(current_index, line_span_end):
                candidate = normalized_lines[idx]
                if not candidate:
                    continue
                score = cls._line_match_score(query_norm, candidate)
                if score > best_score:
                    best_idx = idx
                    best_score = score
                    if score >= 0.995:
                        break

            min_score = 0.52 if len(query_norm) >= 18 else 0.68
            if best_idx >= 0 and best_score >= min_score:
                matched_indexes.append(best_idx)
                matched_chars += len(query_norm)
                current_index = best_idx + 1
            elif matched_indexes:
                current_index = min(search_end, current_index + 4)

        min_required_matches = max(3, min(len(query_lines), max(1, len(query_lines) // 3)))
        if len(matched_indexes) < min_required_matches:
            return None
        if matched_chars / max(total_query_chars, 1) < 0.58:
            return None

        start_idx = matched_indexes[0]
        end_idx = matched_indexes[-1] + 1
        if end_idx <= start_idx:
            return None
        return max(0, start_idx), min(end_idx, len(normalized_lines))

    @classmethod
    def _best_span_from_line_start_candidates(
        cls,
        query_lines: list[str],
        normalized_lines: list[str],
        candidate_starts: list[int],
        preferred_span_len: int,
    ) -> tuple[int, int, float] | None:
        """Score full spans from plausible line starts for long rendered selections."""
        if not query_lines or not candidate_starts:
            return None

        normalized_query = " ".join(query_lines)
        if len(normalized_query) < 48:
            return None

        target_len = max(len(query_lines), preferred_span_len, 1)
        candidate_lengths = {
            max(1, int(target_len * 0.85)),
            target_len,
            int(target_len * 1.05),
            int(target_len * 1.15),
            int(target_len * 1.30),
            int(target_len * 1.50),
            int(target_len * 1.75),
        }

        best_span: tuple[int, int, float] | None = None
        best_score = 0.0
        for start_idx in candidate_starts:
            for span_len in sorted(candidate_lengths):
                end_idx = min(len(normalized_lines), start_idx + span_len)
                if end_idx <= start_idx:
                    continue
                candidate_text = " ".join(line for line in normalized_lines[start_idx:end_idx] if line)
                if not candidate_text:
                    continue
                score = SequenceMatcher(None, normalized_query, candidate_text).ratio()
                relative_len = span_len / max(target_len, 1)
                if relative_len > 1.80:
                    score -= 0.14
                elif relative_len > 1.45:
                    score -= 0.07
                elif relative_len < 0.75:
                    score -= 0.10
                elif relative_len < 0.90:
                    score -= 0.04
                if score > best_score:
                    best_score = score
                    best_span = (start_idx, end_idx, score)

        return best_span

    @classmethod
    def _find_source_span_by_normalized_document_match(
        cls, lines: list[str], query_text: str
    ) -> tuple[int, int, str] | None:
        """Match rendered selection against normalized source text across the whole document."""
        normalized_query = cls._normalize_for_fuzzy_match(query_text)
        if len(normalized_query) < 24:
            return None

        normalized_lines = [cls._normalize_for_fuzzy_match(line) for line in lines]
        source_parts: list[str] = []
        char_to_line: list[int] = []
        for idx, line in enumerate(lines):
            normalized_line = normalized_lines[idx]
            if not normalized_line:
                continue
            if source_parts:
                source_parts.append(" ")
                char_to_line.append(idx)
            source_parts.append(normalized_line)
            char_to_line.extend([idx] * len(normalized_line))

        if not source_parts or not char_to_line:
            return None

        normalized_source = "".join(source_parts)
        query_lines = cls._meaningful_normalized_query_lines(query_text)

        def map_char_span(start_char: int, end_char: int) -> tuple[int, int] | None:
            if start_char < 0 or end_char <= start_char:
                return None
            if start_char >= len(char_to_line):
                return None
            end_char = min(end_char, len(char_to_line))
            start_idx = char_to_line[start_char]
            end_idx = char_to_line[max(start_char, end_char - 1)] + 1
            if start_idx < 0 or end_idx <= start_idx:
                return None
            return start_idx, min(end_idx, len(lines))

        def refine_span(start_idx: int, end_idx: int) -> tuple[int, int]:
            if not query_lines:
                return start_idx, end_idx

            refined_start = start_idx
            refined_end = end_idx
            prefix_candidates = query_lines[: min(8, len(query_lines))]
            suffix_candidates = list(reversed(query_lines[max(0, len(query_lines) - 8) :]))

            def best_line_match(
                candidates: list[str], range_start: int, range_end: int, min_score: float
            ) -> tuple[int, float]:
                best_idx = -1
                best_score = 0.0
                for query_norm in candidates:
                    for idx in range(max(0, range_start), min(len(normalized_lines), range_end)):
                        candidate = normalized_lines[idx]
                        if not candidate:
                            continue
                        score = cls._line_match_score(query_norm, candidate)
                        if score > best_score:
                            best_idx = idx
                            best_score = score
                    if best_idx >= 0 and best_score >= min_score:
                        return best_idx, best_score
                return best_idx, best_score

            start_match_idx, start_score = best_line_match(
                prefix_candidates,
                max(0, start_idx - 10),
                min(len(lines), start_idx + 30),
                0.48,
            )
            if start_match_idx >= 0 and start_score >= 0.48:
                refined_start = start_match_idx

            end_match_idx, end_score = best_line_match(
                suffix_candidates,
                max(refined_start, end_idx - 30),
                min(len(lines), end_idx + 10),
                0.45,
            )
            if end_match_idx >= refined_start and end_score >= 0.45:
                refined_end = end_match_idx + 1

            return refined_start, max(refined_start + 1, min(refined_end, len(lines)))

        found_at = normalized_source.find(normalized_query)
        if found_at != -1:
            mapped = map_char_span(found_at, found_at + len(normalized_query))
            if mapped is not None:
                start_idx, end_idx = refine_span(*mapped)
                aligned = cls._align_query_lines_to_source(query_lines, normalized_lines, start_idx, end_idx)
                if aligned is not None:
                    start_idx, end_idx = aligned
                snippet = "".join(lines[start_idx:end_idx])
                if snippet.strip():
                    return start_idx, end_idx, "normalized"

        # Rendered selections often differ slightly from source due to markdown
        # punctuation stripping. Use multiple anchors from across the normalized
        # selection, project candidate spans back into source space, and score
        # the resulting slices. This is much more resilient than relying on a
        # single prefix anchor.
        anchor_lengths = (320, 240, 180, 120, 80, 48)
        anchor_offsets = [
            0,
            max(0, len(normalized_query) // 4),
            max(0, len(normalized_query) // 2),
            max(0, (len(normalized_query) * 3) // 4),
            max(0, len(normalized_query) - 320),
        ]
        candidate_positions: list[tuple[int, int, int]] = []
        seen_positions: set[tuple[int, int]] = set()
        for offset in anchor_offsets:
            for size in anchor_lengths:
                if len(normalized_query) < size or offset + size > len(normalized_query):
                    continue
                fragment = normalized_query[offset : offset + size]
                search_at = normalized_source.find(fragment)
                hits = 0
                while search_at != -1 and hits < 8:
                    key = (search_at, offset)
                    if key not in seen_positions:
                        seen_positions.add(key)
                        candidate_positions.append((search_at, offset, size))
                    hits += 1
                    search_at = normalized_source.find(fragment, search_at + 1)

        line_start_candidates: list[int] = []
        seen_line_start_buckets: set[int] = set()
        for query_offset, query_norm in enumerate(query_lines[: min(12, len(query_lines))]):
            if len(query_norm) < 4:
                continue
            min_score = 0.52 if len(query_norm) >= 18 else 0.68
            per_query_candidates: list[tuple[float, int]] = []
            for idx, candidate in enumerate(normalized_lines):
                if not candidate:
                    continue
                score = cls._line_match_score(query_norm, candidate)
                if score >= min_score:
                    estimated_start = max(0, idx - query_offset)
                    per_query_candidates.append((score, estimated_start))
            per_query_candidates.sort(key=lambda item: item[0], reverse=True)
            for score, estimated_start in per_query_candidates[:6]:
                bucket = estimated_start // 3
                if bucket in seen_line_start_buckets:
                    continue
                seen_line_start_buckets.add(bucket)
                line_start_candidates.append(estimated_start)

        best_span: tuple[int, int, str] | None = None
        best_score = 0.0
        for position, offset, size in candidate_positions:
            estimated_start = max(0, position - offset)
            estimated_end = min(len(normalized_source), estimated_start + len(normalized_query))
            candidate_text = normalized_source[estimated_start:estimated_end]
            score = SequenceMatcher(None, normalized_query, candidate_text).ratio()
            if estimated_end - estimated_start < len(normalized_query) * 0.72:
                score *= 0.82
            score += min(0.05, size / 6400.0)
            if score <= best_score:
                continue
            mapped = map_char_span(estimated_start, estimated_end)
            if mapped is None:
                continue
            start_idx, end_idx = refine_span(*mapped)
            aligned = cls._align_query_lines_to_source(query_lines, normalized_lines, start_idx, end_idx)
            if aligned is not None:
                start_idx, end_idx = aligned
            snippet = "".join(lines[start_idx:end_idx])
            if not snippet.strip():
                continue
            best_score = score
            best_span = (start_idx, end_idx, "normalized anchor")

        preferred_span_len = (best_span[1] - best_span[0]) if best_span is not None else max(1, len(query_lines))
        candidate_span = cls._best_span_from_line_start_candidates(
            query_lines,
            normalized_lines,
            line_start_candidates[:18],
            preferred_span_len,
        )
        if candidate_span is not None:
            start_idx, end_idx, score = candidate_span
            if score >= 0.86 and score > best_score + 0.015:
                best_score = score
                best_span = (start_idx, end_idx, "normalized lines")

        if best_span is not None and best_score >= 0.74:
            return best_span

        return None

    @classmethod
    def _find_source_span_by_fuzzy_lines(cls, lines: list[str], query_text: str) -> tuple[int, int] | None:
        """Fuzzy-match selected first/last lines against markdown source lines."""
        raw_query_lines = [line.strip() for line in query_text.splitlines() if line.strip()]
        if not raw_query_lines:
            return None

        normalized_lines = [cls._normalize_for_fuzzy_match(line) for line in lines]
        meaningful_query_lines: list[str] = []
        for line in raw_query_lines:
            normalized = cls._normalize_for_fuzzy_match(line)
            if normalized:
                meaningful_query_lines.append(normalized)
        if not meaningful_query_lines:
            return None

        normalized_query = " ".join(meaningful_query_lines)

        def best_line_match(query_norm: str, start_index: int = 0) -> tuple[int, float]:
            best_idx = -1
            best_score = 0.0
            for idx in range(start_index, len(normalized_lines)):
                candidate = normalized_lines[idx]
                if not candidate:
                    continue
                score = cls._line_match_score(query_norm, candidate)
                if score > best_score:
                    best_score = score
                    best_idx = idx
            return best_idx, best_score

        def find_anchor(candidates: list[str], start_index: int, min_score: float) -> tuple[int, float]:
            # Try candidate lines in order and stop at the first sufficiently
            # strong match so non-identifying boundary lines are skipped.
            best_idx = -1
            best_score = 0.0
            for query_norm in candidates:
                idx, score = best_line_match(query_norm, start_index)
                if score > best_score:
                    best_idx = idx
                    best_score = score
                if idx >= 0 and score >= min_score:
                    return idx, score
            return best_idx, best_score

        candidate_starts: list[tuple[float, int]] = []
        seen_candidate_starts: set[int] = set()
        anchor_queries = meaningful_query_lines[: min(8, len(meaningful_query_lines))]
        for query_offset, query_norm in enumerate(anchor_queries):
            if len(query_norm) < 4:
                continue
            min_score = 0.52 if len(query_norm) >= 18 else 0.68
            per_query_candidates: list[tuple[float, int]] = []
            for idx, candidate in enumerate(normalized_lines):
                if not candidate:
                    continue
                score = cls._line_match_score(query_norm, candidate)
                if score >= min_score:
                    estimated_start = max(0, idx - query_offset)
                    per_query_candidates.append((score, estimated_start))
            per_query_candidates.sort(key=lambda item: item[0], reverse=True)
            for score, estimated_start in per_query_candidates[:6]:
                bucket = estimated_start // 3
                if bucket in seen_candidate_starts:
                    continue
                seen_candidate_starts.add(bucket)
                candidate_starts.append((score, estimated_start))

        best_span: tuple[int, int] | None = None
        best_span_score = 0.0
        for anchor_score, estimated_start in sorted(candidate_starts, key=lambda item: item[0], reverse=True)[:18]:
            approx_end = min(len(lines), estimated_start + len(meaningful_query_lines) + 24)
            aligned = cls._align_query_lines_to_source(
                meaningful_query_lines,
                normalized_lines,
                estimated_start,
                approx_end,
            )
            if aligned is None:
                continue
            start_idx, end_idx = aligned
            candidate_text = " ".join(line for line in normalized_lines[start_idx:end_idx] if line)
            if not candidate_text:
                continue
            span_score = SequenceMatcher(None, normalized_query, candidate_text).ratio()
            span_len = max(1, end_idx - start_idx)
            target_len = max(1, len(meaningful_query_lines))
            if span_len > target_len * 1.6:
                span_score -= 0.10
            elif span_len > target_len * 1.25:
                span_score -= 0.04
            elif span_len < target_len * 0.60:
                span_score -= 0.12
            span_score += min(0.04, anchor_score * 0.04)
            if span_score > best_span_score:
                best_span_score = span_score
                best_span = (start_idx, end_idx)

        if best_span is not None and best_span_score >= 0.62:
            return best_span

        start_idx, start_score = find_anchor(meaningful_query_lines, 0, 0.45)
        if start_idx < 0 or start_score < 0.45:
            return None

        end_idx = start_idx + 1
        if len(meaningful_query_lines) > 1:
            end_candidates = list(reversed(meaningful_query_lines))
            end_match_idx, end_score = find_anchor(end_candidates, start_idx, 0.42)
            if end_match_idx >= start_idx and end_score >= 0.42:
                end_idx = end_match_idx + 1
            else:
                approx_span = max(1, len(meaningful_query_lines))
                end_idx = min(len(lines), start_idx + approx_span)

        end_idx = max(start_idx + 1, min(end_idx, len(lines)))
        aligned = cls._align_query_lines_to_source(meaningful_query_lines, normalized_lines, start_idx, end_idx)
        if aligned is not None:
            start_idx, end_idx = aligned
        snippet = "".join(lines[start_idx:end_idx])
        if not snippet.strip():
            return None

        return start_idx, end_idx

    def _set_plain_text_clipboard(self, text: str) -> None:
        """Set clipboard text via Qt, with platform CLI fallback for reliability."""
        clipboard = QApplication.clipboard()
        clipboard.setText(text, QClipboard.Mode.Clipboard)
        clipboard.setText(text, QClipboard.Mode.Selection)
        QApplication.processEvents()

        try:
            if os.environ.get("WAYLAND_DISPLAY") and shutil.which("wl-copy"):
                subprocess.run(["wl-copy"], input=text, text=True, check=False)
                return
            if os.environ.get("DISPLAY") and shutil.which("xclip"):
                subprocess.run(["xclip", "-selection", "clipboard"], input=text, text=True, check=False)
                return
            if os.environ.get("DISPLAY") and shutil.which("xsel"):
                subprocess.run(["xsel", "--clipboard", "--input"], input=text, text=True, check=False)
        except Exception:
            # Qt clipboard already received the text; ignore CLI fallback errors.
            pass

    def _highlight_scope_directory(self) -> Path:
        """Resolve active scope from selected/last-visited directory, then root."""
        index = self.tree.currentIndex()
        if index.isValid():
            selected = Path(self.model.filePath(index))
            if selected.is_dir():
                try:
                    resolved = selected.resolve()
                except Exception:
                    resolved = selected
                self.last_directory_selection = resolved
                return resolved
        if self.last_directory_selection is not None and self.last_directory_selection.is_dir():
            return self.last_directory_selection
        return self.root

    def _update_window_title(self) -> None:
        """Show the effective root in the application window title."""
        scope = self._highlight_scope_directory()
        self.setWindowTitle(f"mdexplore - {scope}")

    def _effective_root_for_persistence(self) -> Path:
        """Resolve persisted root, preferring selected or last visited directory."""
        index = self.tree.currentIndex()
        if index.isValid():
            selected = Path(self.model.filePath(index))
            if selected.is_dir():
                try:
                    return selected.resolve()
                except Exception:
                    return selected
        if self.last_directory_selection is not None and self.last_directory_selection.is_dir():
            return self.last_directory_selection
        return self.root

    def _persist_effective_root(self) -> None:
        """Persist the effective root for future no-argument launches."""
        scope = self._effective_root_for_persistence()
        try:
            self.config_path.write_text(str(scope.resolve()) + "\n", encoding="utf-8")
        except Exception:
            # Requested behavior is resilience; persistence failure should not
            # block application exit.
            pass

    def closeEvent(self, event) -> None:  # noqa: N802
        self._stop_restore_overlay_monitor()
        self._persist_document_view_session()
        self._persist_effective_root()
        self._cleanup_preview_temp_files()
        super().closeEvent(event)

    def _confirm_and_clear_all_highlighting(self) -> None:
        """Prompt and clear all highlight metadata recursively under current scope."""
        scope = self._highlight_scope_directory()
        reply = QMessageBox.question(
            self,
            "Clear All Highlights",
            f"Clear all file highlights recursively under:\n{scope}\n\nThis cannot be undone.",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No,
        )
        if reply != QMessageBox.StandardButton.Yes:
            return

        cleared = self.model.clear_all_highlights(scope)
        self.statusBar().showMessage(
            f"Cleared {cleared} highlight assignment(s) under {scope}",
            4500,
        )

    def _copy_files_to_clipboard(self, files: list[Path]) -> int:
        """Copy file paths to clipboard with file-manager compatible MIME payloads."""
        normalized: list[Path] = []
        seen: set[str] = set()
        for path in files:
            try:
                resolved = path.resolve()
            except Exception:
                resolved = path
            key = str(resolved)
            if key in seen:
                continue
            seen.add(key)
            normalized.append(resolved)

        clipboard = QApplication.clipboard()
        mime_data = QMimeData()
        urls = [QUrl.fromLocalFile(str(path)) for path in normalized]
        mime_data.setUrls(urls)

        # Nemo/Nautilus paste support: this custom format marks clipboard data
        # as file copy operations rather than plain text.
        if urls:
            gnome_payload = "copy\n" + "\n".join(url.toString() for url in urls)
            mime_data.setData("x-special/gnome-copied-files", gnome_payload.encode("utf-8"))

        # Keep plain text for editors/terminals.
        mime_data.setText("\n".join(str(path) for path in normalized))
        clipboard.setMimeData(mime_data)
        return len(normalized)

    def _copy_current_preview_file_to_clipboard(self) -> None:
        """Copy the currently previewed markdown file path to clipboard."""
        if self.current_file is None:
            self.statusBar().showMessage("No previewed markdown file to copy", 3000)
            return

        try:
            target = self.current_file.resolve()
        except Exception:
            target = self.current_file

        if not target.is_file():
            self.statusBar().showMessage("Previewed file is unavailable", 3000)
            return

        copied = self._copy_files_to_clipboard([target])
        if copied:
            self.statusBar().showMessage(f"Copied previewed file to clipboard: {target.name}", 4000)

    def _copy_highlighted_files_to_clipboard(self, color_value: str, color_name: str) -> None:
        """Copy highlighted file paths for a color to the system clipboard."""
        scope = self._highlight_scope_directory()
        matches = self.model.collect_files_with_color(scope, color_value)
        copied = self._copy_files_to_clipboard(matches)
        self.statusBar().showMessage(
            f"Copied {copied} {color_name.lower()} highlighted file(s) from {scope}",
            4000,
        )

    def _on_tree_selection_changed(self, current, _previous) -> None:
        # Any selection transition means the user is leaving the previous
        # document/scope, so immediately clear restore UI state.
        self._stop_restore_overlay_monitor()
        path = Path(self.model.filePath(current))
        self._update_window_title()
        if path.is_dir():
            try:
                self.last_directory_selection = path.resolve()
            except Exception:
                self.last_directory_selection = path
            self._rerun_active_search_for_scope()
            return
        if not path.is_file() or path.suffix.lower() != ".md":
            return
        self.statusBar().showMessage(f"Loading preview: {path.name}...")
        self._load_preview(path)

    def _on_preview_render_finished(
        self,
        request_id: int,
        path_key: str,
        html_doc: str,
        mtime_ns: int,
        size: int,
        error_text: str,
    ) -> None:
        """Apply finished background render if it is still the active request."""
        worker_to_remove = None
        for worker in self._active_render_workers:
            if worker.request_id == request_id:
                worker_to_remove = worker
                break
        if worker_to_remove is not None:
            self._active_render_workers.remove(worker_to_remove)

        if request_id != self._render_request_id:
            return

        if self.current_file is None:
            return
        try:
            current_key = str(self.current_file.resolve())
        except Exception:
            current_key = str(self.current_file)
        if current_key != path_key:
            return

        if error_text:
            self.statusBar().showMessage(f"Preview render failed: {error_text}", 5000)
            html_doc = self._placeholder_html(f"Could not render preview for {self.current_file.name}: {error_text}")
        else:
            self.cache[path_key] = (mtime_ns, size, html_doc)
            self._set_current_preview_signature(path_key, int(mtime_ns), int(size))
            self.statusBar().showMessage(f"Preview rendered: {self.current_file.name}")

        try:
            base_url = QUrl.fromLocalFile(f"{self.current_file.parent.resolve()}/")
        except Exception:
            base_url = QUrl.fromLocalFile(f"{self.root}/")
        self._set_preview_html(self._inject_mermaid_cache_seed(html_doc, path_key), base_url)

    @staticmethod
    def _doc_id_for_path(path_key: str) -> str:
        return hashlib.sha1(path_key.encode("utf-8", errors="replace")).hexdigest()[:12]

    def _current_preview_path_key(self) -> str | None:
        if self.current_file is None:
            return None
        try:
            return str(self.current_file.resolve())
        except Exception:
            return str(self.current_file)

    def _clear_current_preview_signature(self) -> None:
        """Drop tracked mtime/size signature for the active preview file."""
        self._current_preview_signature_key = None
        self._current_preview_signature = None

    def _set_current_preview_signature(self, path_key: str, mtime_ns: int, size: int) -> None:
        """Record the latest observed on-disk signature for a previewed file."""
        self._current_preview_signature_key = path_key
        self._current_preview_signature = (int(mtime_ns), int(size))

    def _on_file_change_watch_tick(self) -> None:
        """Auto-refresh preview when the active markdown file changes on disk."""
        if self.current_file is None:
            return

        try:
            resolved = self.current_file.resolve()
            path_key = str(resolved)
        except Exception:
            resolved = self.current_file
            path_key = str(self.current_file)

        try:
            stat = resolved.stat()
        except Exception:
            # File may be temporarily inaccessible while external tools save.
            return

        current_sig = (int(stat.st_mtime_ns), int(stat.st_size))
        if self._current_preview_signature_key != path_key or self._current_preview_signature is None:
            self._set_current_preview_signature(path_key, current_sig[0], current_sig[1])
            return
        if current_sig == self._current_preview_signature:
            return

        # Update baseline first so repeated timer ticks during one save do not
        # trigger duplicate refresh cycles.
        self._set_current_preview_signature(path_key, current_sig[0], current_sig[1])
        self._refresh_current_preview(reason="file changed on disk")

    def _has_saved_scroll_for_current_preview(self) -> bool:
        key = self._current_preview_scroll_key()
        if key is None:
            return False
        if key in self._preview_scroll_positions:
            return True
        # Backward compatibility with pre-view-tab scroll cache entries.
        path_key = self._current_preview_path_key()
        return bool(path_key and path_key in self._preview_scroll_positions)

    def _capture_current_preview_scroll(self, force: bool = False) -> None:
        """Capture current preview scroll position for the selected file."""
        scroll_key = self._current_preview_scroll_key()
        if scroll_key is None:
            return
        if not force:
            if not self._preview_capture_enabled:
                return
            if time.monotonic() < self._scroll_restore_block_until:
                return
        # Use Qt's synchronous scrollPosition() to avoid async JS race conditions
        # during rapid file switches.
        try:
            pos = self.preview.page().scrollPosition()
            y = float(pos.y())
        except Exception:
            return
        if math.isfinite(y):
            self._preview_scroll_positions[scroll_key] = y
            state = self._current_view_state()
            if state is not None:
                state["scroll_y"] = y
            self._request_active_view_top_line_update(force=force)

    def _enable_preview_scroll_capture_for(self, expected_key: str) -> None:
        """Re-enable periodic scroll capture for the currently displayed file."""
        if self._current_preview_path_key() != expected_key:
            return
        self._preview_capture_enabled = True
        self._scroll_restore_block_until = 0.0
        self._capture_current_preview_scroll(force=True)
        self._capture_current_diagram_view_state(expected_key)
        self._request_active_view_top_line_update(force=True)

    def _restore_current_preview_scroll(self, expected_key: str | None = None) -> None:
        """Restore previously captured scroll position for the selected file."""
        path_key = self._current_preview_path_key()
        if path_key is None:
            return
        if expected_key is not None and path_key != expected_key:
            return
        scroll_key = self._current_preview_scroll_key()
        scroll_y = self._preview_scroll_positions.get(scroll_key) if scroll_key is not None else None
        if scroll_y is None:
            state = self._current_view_state()
            if state is not None:
                try:
                    scroll_y = float(state.get("scroll_y", 0.0))
                except Exception:
                    scroll_y = 0.0
        if scroll_y is None:
            # Backward compatibility with pre-view-tab scroll cache entries.
            scroll_y = self._preview_scroll_positions.get(path_key)
        if scroll_y is None:
            return
        scroll_json = json.dumps(float(scroll_y))
        js = f"""
(() => {{
  const y = {scroll_json};
  // Apply twice (RAF + timeout) because late layout work can override scroll.
  requestAnimationFrame(() => window.scrollTo(0, y));
  setTimeout(() => window.scrollTo(0, y), 60);
}})();
"""
        # Mutates page scroll position (no returned data consumed).
        self.preview.page().runJavaScript(js)
        self._request_active_view_top_line_update(force=True)

    @staticmethod
    def _truncate_error_text(text: str, max_len: int = 1200) -> str:
        normalized = text.replace("\r\n", "\n").replace("\r", "\n").strip()
        if len(normalized) <= max_len:
            return normalized
        return normalized[: max_len - 4] + "\n..."

    def _plantuml_inner_html(self, status: str, payload: str) -> str:
        if status == "done":
            return f'<img class="plantuml" src="{payload}" alt="PlantUML diagram"/>'
        safe_error = html.escape(self._truncate_error_text(payload or "unknown error"))
        return (
            '<div class="plantuml-error-message">PlantUML render failed with error:</div>'
            f'<pre class="plantuml-error-detail">{safe_error}</pre>'
        )

    def _plantuml_block_html(
        self,
        placeholder_id: str,
        line_attrs: str,
        status: str,
        payload: str,
        hash_key: str | None = None,
    ) -> str:
        inner = self._plantuml_inner_html(status, payload) if status in {"done", "error"} else "PlantUML rendering..."
        classes = ["mdexplore-fence", "plantuml-async"]
        if status == "pending":
            classes.append("plantuml-pending")
        elif status == "error":
            classes.append("plantuml-error")
        else:
            classes.append("plantuml-ready")
        class_attr = " ".join(classes)
        hash_attr = ""
        if hash_key:
            safe_hash = html.escape(hash_key, quote=True)
            hash_attr = f' data-mdexplore-plantuml-hash="{safe_hash}"'
        return (
            f'<div class="{class_attr}" id="{placeholder_id}"{hash_attr}{line_attrs}>'
            f"{inner}"
            "</div>\n"
        )

    def _ensure_plantuml_render_started(self, hash_key: str, prepared_code: str) -> None:
        result = self._plantuml_results.get(hash_key)
        if result is not None and result[0] in {"done", "error"}:
            return
        if hash_key in self._plantuml_inflight:
            return

        # Deduplicate renders: identical diagram source only renders once.
        self._plantuml_inflight.add(hash_key)
        self._plantuml_results[hash_key] = ("pending", "")
        worker = PlantUmlRenderWorker(
            hash_key,
            prepared_code,
            self.renderer._plantuml_jar_path,
            self.renderer._plantuml_setup_issue,
        )
        self._active_plantuml_workers.add(worker)
        worker.signals.finished.connect(self._on_plantuml_render_finished)
        self._plantuml_pool.start(worker)

    def _on_plantuml_render_finished(self, hash_key: str, status: str, payload: str) -> None:
        worker_to_remove = None
        for worker in self._active_plantuml_workers:
            if worker.hash_key == hash_key:
                worker_to_remove = worker
                break
        if worker_to_remove is not None:
            self._active_plantuml_workers.remove(worker_to_remove)

        self._plantuml_inflight.discard(hash_key)
        final_status = "done" if status == "done" else "error"
        self._plantuml_results[hash_key] = (final_status, payload)

        # Any cached document snapshot that references this diagram is stale
        # until placeholders are replaced with the final result.
        for doc_key in self._plantuml_docs_by_hash.get(hash_key, set()):
            self.cache.pop(doc_key, None)

        self._apply_plantuml_result_to_current_preview(hash_key)
        current_key = self._current_preview_path_key()
        if current_key is not None:
            current_placeholders = self._plantuml_placeholders_by_doc.get(current_key, {})
            if hash_key in current_placeholders:
                self._show_preview_progress_status()
                self._check_restore_overlay_progress()

    def _apply_plantuml_result_to_current_preview(self, hash_key: str) -> None:
        if self.current_file is None:
            return
        try:
            current_key = str(self.current_file.resolve())
        except Exception:
            current_key = str(self.current_file)

        placeholders_by_hash = self._plantuml_placeholders_by_doc.get(current_key, {})
        placeholder_ids = placeholders_by_hash.get(hash_key, [])
        if not placeholder_ids:
            return

        status, payload = self._plantuml_results.get(hash_key, ("pending", ""))
        if status not in {"done", "error"}:
            return
        if status == "done":
            class_name = "plantuml-ready"
            inner_html = self._plantuml_inner_html("done", payload)
        else:
            class_name = "plantuml-error"
            inner_html = self._plantuml_inner_html("error", payload)

        ids_json = json.dumps(placeholder_ids)
        html_json = json.dumps(inner_html)
        class_json = json.dumps(class_name)
        # Patch nodes in place to preserve scroll position and selection state.
        js = f"""
(() => {{
  const ids = {ids_json};
  const inner = {html_json};
  const className = {class_json};
  // Only touch known placeholder nodes so unrelated page state is untouched.
  for (const id of ids) {{
    const node = document.getElementById(id);
    if (!node) continue;
    node.classList.remove("plantuml-pending", "plantuml-ready", "plantuml-error");
    node.classList.add(className);
    node.innerHTML = inner;
  }}
  if (window.__mdexploreApplyPlantUmlZoomControls) {{
    window.__mdexploreApplyPlantUmlZoomControls("auto");
  }}
  for (const shell of Array.from(document.querySelectorAll(".mdexplore-mermaid-shell"))) {{
    const fn = shell && shell.__mdexploreReapplySavedState;
    if (typeof fn !== "function") {{
      continue;
    }}
    try {{
      fn();
    }} catch (_error) {{
      // Ignore per-shell restore failures.
    }}
  }}
}})();
"""
        # Mutates only known PlantUML placeholder nodes in the active page.
        self.preview.page().runJavaScript(js)

    def _apply_all_ready_plantuml_to_current_preview(self) -> None:
        if self.current_file is None:
            return
        try:
            current_key = str(self.current_file.resolve())
        except Exception:
            current_key = str(self.current_file)

        placeholders_by_hash = self._plantuml_placeholders_by_doc.get(current_key, {})
        ready_hashes: list[str] = []
        for hash_key in placeholders_by_hash:
            status, _payload = self._plantuml_results.get(hash_key, ("pending", ""))
            if status in {"done", "error"}:
                ready_hashes.append(hash_key)

        if not ready_hashes:
            return

        batch_size = max(1, int(PLANTUML_RESTORE_BATCH_SIZE))

        def apply_batch(start_index: int) -> None:
            if self._current_preview_path_key() != current_key:
                return
            end_index = min(len(ready_hashes), start_index + batch_size)
            for hash_key in ready_hashes[start_index:end_index]:
                self._apply_plantuml_result_to_current_preview(hash_key)
            if end_index < len(ready_hashes):
                QTimer.singleShot(0, lambda next_index=end_index: apply_batch(next_index))

        apply_batch(0)

    def _load_preview(self, path: Path) -> None:
        # Render markdown quickly with async PlantUML placeholders so the
        # document appears immediately while diagrams render in background.
        self._stop_restore_overlay_monitor()
        previous_path_key = self._current_preview_path_key()
        next_path_key = self._path_key(path)
        self._capture_current_preview_scroll(force=True)
        if previous_path_key is not None and previous_path_key != next_path_key:
            # Best-effort capture only: file switching should stay responsive
            # even if the embedded page is busy finishing diagram work.
            self._capture_current_diagram_view_state_blocking(previous_path_key, timeout_ms=90)
            self._persist_document_view_session(previous_path_key)
        self._cancel_pending_preview_render()
        self._preview_capture_enabled = False
        self._scroll_restore_block_until = 0.0
        if previous_path_key != next_path_key:
            self._load_persisted_document_view_session(next_path_key)
            restored = self._restore_document_view_session(next_path_key)
            if not restored:
                self._reset_document_views(initial_scroll=0.0, initial_line=1)
        should_highlight_search = bool(self.match_input.text().strip()) and self._is_path_in_current_matches(path)
        self._pending_preview_search_terms = self._current_search_terms() if should_highlight_search else []
        self._pending_preview_search_close_groups = self._current_close_term_groups() if should_highlight_search else []
        self.statusBar().showMessage(f"Loading preview content: {path.name}...")

        self.current_file = path
        self._refresh_tree_multi_view_markers()
        # Explicitly clear any stale overlay at document entry before
        # considering whether the new document needs one.
        self._stop_restore_overlay_monitor()
        self._current_document_total_lines = max(1, int(self._document_line_counts.get(next_path_key, 1)))
        self._sync_all_view_tab_progress()
        self._update_view_tabs_visibility()
        self._update_add_view_button_state()
        try:
            rel = path.relative_to(self.root)
            self.path_label.setText(str(rel))
        except ValueError:
            self.path_label.setText(str(path))

        try:
            base_url = QUrl.fromLocalFile(f"{path.parent.resolve()}/")
        except Exception:
            base_url = QUrl.fromLocalFile(f"{self.root}/")

        try:
            resolved = path.resolve()
            stat = resolved.stat()
            cache_key = str(resolved)
            self._set_current_preview_signature(cache_key, int(stat.st_mtime_ns), int(stat.st_size))
            cached = self.cache.get(cache_key)
            if cached and cached[0] == stat.st_mtime_ns and cached[1] == stat.st_size:
                has_math, has_mermaid, has_plantuml = self._detect_special_features_for_path(
                    resolved,
                    cached_html=cached[2],
                )
                self._begin_restore_overlay_monitor(
                    cache_key,
                    needs_math=has_math,
                    needs_mermaid=has_mermaid,
                    needs_plantuml=has_plantuml,
                    phase="restoring",
                )
                self.statusBar().showMessage(f"Using cached preview: {resolved.name}...")
                self._set_preview_html(self._inject_mermaid_cache_seed(cached[2], cache_key), base_url)
                return

            self.statusBar().showMessage(f"Rendering markdown: {resolved.name}...")
            markdown_text = resolved.read_text(encoding="utf-8", errors="replace")
            total_lines = self._count_markdown_lines(markdown_text)
            self._document_line_counts[cache_key] = total_lines
            self._current_document_total_lines = total_lines
            self._sync_all_view_tab_progress()
            doc_id = self._doc_id_for_path(cache_key)

            # Remove stale dependency links for this document before rebuilding.
            previous_placeholders = self._plantuml_placeholders_by_doc.get(cache_key, {})
            for hash_key in previous_placeholders:
                docs = self._plantuml_docs_by_hash.get(hash_key)
                if docs is not None:
                    docs.discard(cache_key)
                    if not docs:
                        self._plantuml_docs_by_hash.pop(hash_key, None)

            placeholders_by_hash: dict[str, list[str]] = {}

            def plantuml_resolver(code: str, index: int, line_attrs: str) -> str:
                # Stable hash key lets the same diagram result be reused across
                # multiple files and repeated blocks.
                prepared_code = self.renderer._prepare_plantuml_source(code)
                hash_key = hashlib.sha1(prepared_code.encode("utf-8", errors="replace")).hexdigest()
                placeholder_id = f"mdexplore-plantuml-{doc_id}-{index}"

                placeholders_by_hash.setdefault(hash_key, []).append(placeholder_id)
                self._plantuml_docs_by_hash.setdefault(hash_key, set()).add(cache_key)

                status, payload = self._plantuml_results.get(hash_key, ("pending", ""))
                if status not in {"done", "error"}:
                    self._ensure_plantuml_render_started(hash_key, prepared_code)
                # Always emit a lightweight placeholder first so file restores
                # are immediate; ready/error SVG payloads are patched in after
                # the page mounts.
                return self._plantuml_block_html(placeholder_id, line_attrs, "pending", "", hash_key=hash_key)

            html_doc = self.renderer.render_document(
                markdown_text,
                resolved.name,
                total_lines=total_lines,
                plantuml_resolver=plantuml_resolver,
            )
            self._merge_renderer_pdf_mermaid_cache_seed()
            self._plantuml_placeholders_by_doc[cache_key] = placeholders_by_hash
            self.cache[cache_key] = (stat.st_mtime_ns, stat.st_size, html_doc)
            self.statusBar().showMessage(f"Preview rendered, loading in viewer: {resolved.name}...")
            self._set_preview_html(self._inject_mermaid_cache_seed(html_doc, cache_key), base_url)
        except Exception as exc:
            self._stop_restore_overlay_monitor()
            self.statusBar().showMessage(f"Preview render failed: {exc}", 5000)
            self._set_preview_html(
                self._placeholder_html(f"Could not render preview for {path.name}: {exc}"),
                base_url,
            )

    def _refresh_current_preview(self, _checked: bool = False, *, reason: str | None = None) -> None:
        """Force re-render of the currently selected file."""
        if self.current_file is None:
            return
        try:
            cache_key = str(self.current_file.resolve())
        except Exception:
            cache_key = str(self.current_file)
        self.cache.pop(cache_key, None)
        self.statusBar().showMessage(f"Refreshing preview: {self.current_file.name}...")
        self._load_preview(self.current_file)
        if reason:
            self.statusBar().showMessage(
                f"Auto-refreshed preview: {self.current_file.name} ({reason})",
                4500,
            )

    def _set_pdf_export_busy(self, busy: bool) -> None:
        """Toggle PDF export UI state while async export is running."""
        self._pdf_export_in_progress = busy
        self.pdf_btn.setEnabled(not busy)

    def _export_current_preview_pdf(self) -> None:
        """Export the currently previewed markdown rendering to a numbered PDF."""
        if self.current_file is None:
            QMessageBox.information(self, "No file selected", "Select a markdown file before exporting to PDF.")
            return
        if self._pdf_export_in_progress:
            self.statusBar().showMessage("PDF export already in progress", 3000)
            return

        try:
            source_path = self.current_file.resolve()
        except Exception:
            source_path = self.current_file
        source_key = str(source_path)
        output_path = source_path.with_suffix(".pdf")
        self._pdf_export_source_key = source_key
        self._pending_pdf_layout_hints = {}
        # Preserve current diagram zoom/pan before forcing PDF-safe rendering mode.
        self._capture_current_diagram_view_state_blocking(source_key, timeout_ms=500)
        self._capture_current_diagram_view_state(source_key)

        self._set_pdf_export_busy(True)
        self.statusBar().showMessage(f"Preparing PDF for {source_path.name}...")
        self._prepare_preview_for_pdf_export(output_path, attempt=0, source_key=source_key)

    def _prepare_preview_for_pdf_export(self, output_path: Path, attempt: int, source_key: str) -> None:
        """Wait for math/Mermaid/fonts readiness and inject print style before export."""
        js = """
(() => {
  // Print-only math tuning to avoid cramped/squished glyph appearance in PDF.
  if (!document.getElementById("__mdexplore_pdf_math_style")) {
    const style = document.createElement("style");
    style.id = "__mdexplore_pdf_math_style";
    style.textContent = `
@media print {
  @page {
    size: Letter portrait;
  }
  @page mdexploreLandscape {
    size: Letter landscape;
  }
  main {
    max-width: none !important;
    width: auto !important;
    margin: 0 !important;
    padding: 1.1rem 0.9rem 4rem 0.9rem !important;
  }
  .mdexplore-print-block {
    display: block;
    margin-left: auto !important;
    margin-right: auto !important;
  }
  .mdexplore-print-block.mdexplore-print-keep {
    break-inside: avoid-page !important;
    page-break-inside: avoid !important;
  }
  .mdexplore-print-block.mdexplore-print-heading-keep {
    break-inside: avoid-page !important;
    page-break-inside: avoid !important;
  }
  .mdexplore-print-block.mdexplore-print-break-before {
    break-before: page !important;
    page-break-before: always !important;
  }
  .mdexplore-fence.mdexplore-print-break-before {
    display: block !important;
    break-before: page !important;
    page-break-before: always !important;
  }
  .mdexplore-print-sequence-page-break {
    display: block !important;
    height: 0 !important;
    margin: 0 !important;
    padding: 0 !important;
    break-before: page !important;
    page-break-before: always !important;
  }
  hr.mdexplore-print-skip {
    display: none !important;
  }
  .mdexplore-print-block.mdexplore-print-landscape-page {
    page: mdexploreLandscape;
    break-before: page;
    page-break-before: always;
    break-after: page;
    page-break-after: always;
  }
  .mdexplore-print-block.mdexplore-print-landscape-page:last-child {
    break-after: auto;
    page-break-after: auto;
  }
  .mdexplore-print-heading-anchor {
    break-after: avoid-page;
    page-break-after: avoid;
  }
  .mdexplore-print-heading-break-before {
    break-before: page !important;
    page-break-before: always !important;
  }
  .mdexplore-print-heading-landscape {
    page: mdexploreLandscape;
  }
  .mdexplore-print-heading-landscape + .mdexplore-fence.mdexplore-print-landscape-page,
  .mdexplore-print-heading-landscape + .mdexplore-print-block.mdexplore-print-landscape-page {
    break-before: avoid-page !important;
    page-break-before: avoid !important;
  }
  .mdexplore-fence.mdexplore-print-with-heading {
    break-before: avoid-page;
    page-break-before: avoid;
  }
  .mdexplore-fence {
    margin-left: auto !important;
    margin-right: auto !important;
  }
  .mdexplore-fence.mdexplore-print-keep {
    display: inline-block !important;
    break-inside: avoid-page !important;
    page-break-inside: avoid !important;
  }
  .mdexplore-fence.mdexplore-print-landscape-page {
    page: mdexploreLandscape;
    break-before: page;
    page-break-before: always;
    break-after: page;
    page-break-after: always;
  }
  .mdexplore-fence.mdexplore-print-landscape-page:last-child {
    break-after: auto;
    page-break-after: auto;
  }
  .mdexplore-fence.mdexplore-print-keep .mermaid,
  .mdexplore-fence.mdexplore-print-keep img.plantuml,
  .mdexplore-fence.mdexplore-print-keep svg.mdexplore-plantuml-inline,
  .mdexplore-fence.mdexplore-print-keep .mermaid svg {
    break-inside: avoid-page !important;
    page-break-inside: avoid !important;
  }
  .mdexplore-fence.mdexplore-print-allow-break {
    break-inside: auto !important;
    page-break-inside: auto !important;
  }
  .mdexplore-fence .mermaid {
    display: block;
    width: 100% !important;
    max-width: 100% !important;
    min-height: var(--mdexplore-print-diagram-reserved-height, auto);
  }
  .mdexplore-fence img.plantuml,
  .mdexplore-fence svg.mdexplore-plantuml-inline {
    display: block;
    width: var(--mdexplore-print-diagram-width, auto) !important;
    max-width: var(--mdexplore-print-diagram-max-width, 100%) !important;
    height: var(--mdexplore-print-diagram-height, auto) !important;
    margin: 0 auto !important;
  }
  .mdexplore-fence {
    width: var(--mdexplore-print-section-width, auto) !important;
    max-width: 100% !important;
    min-height: var(--mdexplore-print-diagram-reserved-height, auto);
  }
  .mdexplore-fence .mermaid svg {
    display: block;
    width: var(--mdexplore-print-diagram-width, auto) !important;
    max-width: var(--mdexplore-print-diagram-max-width, 100%) !important;
    height: var(--mdexplore-print-diagram-height, auto) !important;
    margin: 0 auto !important;
  }
  .mdexplore-fence.mdexplore-print-keep img.plantuml,
  .mdexplore-fence.mdexplore-print-keep svg.mdexplore-plantuml-inline,
  .mdexplore-fence.mdexplore-print-keep .mermaid svg {
    max-height: var(--mdexplore-print-diagram-max-height, 86vh) !important;
    object-fit: contain;
  }
  .mdexplore-fence.mdexplore-print-allow-break img.plantuml,
  .mdexplore-fence.mdexplore-print-allow-break svg.mdexplore-plantuml-inline,
  .mdexplore-fence.mdexplore-print-allow-break .mermaid svg {
    max-height: none !important;
  }
  main img:not(.plantuml) {
    display: block !important;
    width: auto !important;
    max-width: 100% !important;
    height: auto !important;
  }
  pre {
    overflow: visible !important;
    max-width: 100% !important;
    white-space: pre-wrap !important;
    overflow-wrap: anywhere !important;
    word-break: break-word !important;
  }
  pre > code,
  pre code,
  code[class*="language-"],
  pre code[class*="language-"] {
    white-space: pre-wrap !important;
    overflow-wrap: anywhere !important;
    word-break: break-word !important;
  }
  pre::-webkit-scrollbar {
    width: 0 !important;
    height: 0 !important;
    display: none !important;
  }
  mjx-container[jax="SVG"] {
    font-size: 1.08em !important;
    text-rendering: geometricPrecision;
    page-break-inside: avoid;
    break-inside: avoid;
  }
  mjx-container[jax="SVG"] > svg {
    overflow: visible;
    shape-rendering: geometricPrecision;
    text-rendering: geometricPrecision;
  }
  mjx-container[jax="SVG"][display="true"] {
    margin: 0.9em 0 1.05em 0 !important;
  }
  mjx-container[jax="CHTML"] {
    font-family: "STIX Two Math", "STIXGeneral", "Cambria Math", "Noto Sans Math", "Latin Modern Math", serif !important;
    font-kerning: normal !important;
    text-rendering: geometricPrecision;
  }
  mjx-container[jax="CHTML"] mjx-mi,
  mjx-container[jax="CHTML"] mjx-mo,
  mjx-container[jax="CHTML"] mjx-mn,
  mjx-container[jax="CHTML"] mjx-mtext {
    letter-spacing: 0.01em !important;
  }
}
`;
    document.head.appendChild(style);
  }

  if (document.documentElement) {
    document.documentElement.classList.add("mdexplore-pdf-export-mode");
  }
  document.body.classList.add("mdexplore-pdf-export-mode");
  if (!document.getElementById("__mdexplore_pdf_mermaid_light_override")) {
    const style = document.createElement("style");
    style.id = "__mdexplore_pdf_mermaid_light_override";
    style.textContent = `
body.mdexplore-pdf-export-mode .mdexplore-mermaid-toolbar {
  display: none !important;
}
body.mdexplore-pdf-export-mode .mdexplore-mermaid-viewport {
  overflow: hidden !important;
  scrollbar-width: none !important;
  -ms-overflow-style: none !important;
}
html.mdexplore-pdf-export-mode,
body.mdexplore-pdf-export-mode {
  --fg: #1a1a1a !important;
  --bg: #ffffff !important;
  --code-bg: #efefef !important;
  --border: #7a7a7a !important;
  --link: #2d2d2d !important;
  --callout-note-border: #666666 !important;
  --callout-note-bg: #f2f2f2 !important;
  --callout-tip-border: #666666 !important;
  --callout-tip-bg: #f2f2f2 !important;
  --callout-important-border: #666666 !important;
  --callout-important-bg: #f2f2f2 !important;
  --callout-warning-border: #666666 !important;
  --callout-warning-bg: #f2f2f2 !important;
  --callout-caution-border: #666666 !important;
  --callout-caution-bg: #f2f2f2 !important;
  color: #1a1a1a !important;
  background: #ffffff !important;
}
html.mdexplore-pdf-export-mode,
body.mdexplore-pdf-export-mode main {
  color: #1a1a1a !important;
  background: #ffffff !important;
}
body.mdexplore-pdf-export-mode a {
  color: #2d2d2d !important;
}
body.mdexplore-pdf-export-mode code,
body.mdexplore-pdf-export-mode pre {
  color: #1a1a1a !important;
  background: #efefef !important;
  border-color: #7a7a7a !important;
}
body.mdexplore-pdf-export-mode pre {
  overflow: visible !important;
  max-width: 100% !important;
  white-space: pre-wrap !important;
  overflow-wrap: anywhere !important;
  word-break: break-word !important;
}
body.mdexplore-pdf-export-mode pre > code,
body.mdexplore-pdf-export-mode pre code,
body.mdexplore-pdf-export-mode code[class*="language-"],
body.mdexplore-pdf-export-mode pre code[class*="language-"] {
  white-space: pre-wrap !important;
  overflow-wrap: anywhere !important;
  word-break: break-word !important;
}
body.mdexplore-pdf-export-mode pre::-webkit-scrollbar {
  width: 0 !important;
  height: 0 !important;
  display: none !important;
}
body.mdexplore-pdf-export-mode main {
  max-width: none !important;
  width: auto !important;
  margin: 0 !important;
  padding: 1.1rem 0.9rem 4rem 0.9rem !important;
}
body.mdexplore-pdf-export-mode main img:not(.plantuml) {
  display: block !important;
  width: auto !important;
  max-width: 100% !important;
  height: auto !important;
}
body.mdexplore-pdf-export-mode table,
body.mdexplore-pdf-export-mode th,
body.mdexplore-pdf-export-mode td,
body.mdexplore-pdf-export-mode blockquote,
body.mdexplore-pdf-export-mode .mdexplore-callout,
body.mdexplore-pdf-export-mode .mdexplore-fence {
  border-color: #7a7a7a !important;
}
`;
    document.head.appendChild(style);
  }

  const decodeSvgDataUriForPdf = (src) => {
    const raw = String(src || "");
    if (!raw.startsWith("data:image/svg+xml")) {
      return "";
    }
    const commaIndex = raw.indexOf(",");
    if (commaIndex < 0) {
      return "";
    }
    const meta = raw.slice(0, commaIndex).toLowerCase();
    const payload = raw.slice(commaIndex + 1);
    try {
      if (meta.includes(";base64")) {
        return atob(payload);
      }
      return decodeURIComponent(payload);
    } catch (_error) {
      return "";
    }
  };

  const intrinsicSvgSizeFromNodeForPdf = (svg) => {
    if (!(svg instanceof SVGElement)) {
      return { width: 0, height: 0 };
    }
    const viewBox = String(svg.getAttribute("viewBox") || "").trim();
    if (viewBox) {
      const parts = viewBox.split(/[\\s,]+/).map((part) => Number.parseFloat(part));
      if (parts.length === 4 && parts.every((num) => Number.isFinite(num))) {
        const width = Math.abs(parts[2]);
        const height = Math.abs(parts[3]);
        if (width > 0 && height > 0) {
          return { width, height };
        }
      }
    }
    const width = Number.parseFloat(String(svg.getAttribute("width") || "").replace(/px$/i, ""));
    const height = Number.parseFloat(String(svg.getAttribute("height") || "").replace(/px$/i, ""));
    if (Number.isFinite(width) && Number.isFinite(height) && width > 0 && height > 0) {
      return { width, height };
    }
    return { width: 0, height: 0 };
  };

  const normalizePlantUmlInlineSvgForPdf = (svg) => {
    if (!(svg instanceof SVGElement)) {
      return;
    }
    svg.classList.add("plantuml", "mdexplore-plantuml-inline");
    svg.style.removeProperty("transform");
    svg.style.setProperty("display", "block", "important");
    svg.style.setProperty("width", "var(--mdexplore-print-diagram-width, auto)", "important");
    svg.style.setProperty("max-width", "var(--mdexplore-print-diagram-max-width, 100%)", "important");
    svg.style.setProperty("height", "var(--mdexplore-print-diagram-height, auto)", "important");
    svg.style.setProperty("max-height", "var(--mdexplore-print-diagram-max-height, none)", "important");
    svg.style.setProperty("margin", "0 auto", "important");
  };

  const replacePlantUmlImageWithInlineSvgForPdf = (img) => {
    if (!(img instanceof HTMLImageElement)) {
      return null;
    }
    if (img.dataset.mdexplorePlantumlInline === "1") {
      return null;
    }
    const markup = decodeSvgDataUriForPdf(img.currentSrc || img.src || "");
    if (!markup) {
      return null;
    }
    try {
      const template = document.createElement("template");
      template.innerHTML = markup.trim();
      const svg = template.content.firstElementChild;
      if (!(svg instanceof SVGElement) || String(svg.tagName || "").toLowerCase() !== "svg") {
        return null;
      }
      const replacement = svg;
      replacement.setAttribute("data-mdexplore-original-img", img.outerHTML);
      replacement.setAttribute("data-mdexplorePlantumlInline", "1");
      replacement.dataset.mdexplorePlantumlInline = "1";
      normalizePlantUmlInlineSvgForPdf(replacement);
      img.replaceWith(replacement);
      return replacement;
    } catch (_error) {
      return null;
    }
  };

  const normalizeDiagramStateForPdf = () => {
    // Flatten interactive wrappers so current scroll/pan/zoom cannot leak into PDF.
    for (const shell of Array.from(document.querySelectorAll(".mdexplore-mermaid-shell"))) {
      if (!(shell instanceof HTMLElement)) {
        continue;
      }
      const host = shell.parentElement;
      if (!(host instanceof HTMLElement)) {
        continue;
      }
      host.style.setProperty("display", "block", "important");
      host.style.setProperty("width", "100%", "important");
      host.style.setProperty("max-width", "100%", "important");
      const viewport = shell.querySelector(".mdexplore-mermaid-viewport");
      const svg = viewport instanceof HTMLElement ? viewport.querySelector("svg") : shell.querySelector("svg");
      const plantImg =
        viewport instanceof HTMLElement ? viewport.querySelector("img.plantuml") : shell.querySelector("img.plantuml");
      const plantSvg =
        viewport instanceof HTMLElement
          ? viewport.querySelector("svg.mdexplore-plantuml-inline")
          : shell.querySelector("svg.mdexplore-plantuml-inline");
      if (svg instanceof SVGElement) {
        svg.style.removeProperty("transform");
        svg.removeAttribute("width");
        svg.removeAttribute("height");
        svg.style.removeProperty("width");
        svg.style.setProperty("width", "var(--mdexplore-print-diagram-width, auto)", "important");
        svg.style.setProperty("max-width", "var(--mdexplore-print-diagram-max-width, 100%)", "important");
        svg.style.setProperty("height", "var(--mdexplore-print-diagram-height, auto)", "important");
        svg.style.setProperty("max-height", "var(--mdexplore-print-diagram-max-height, none)", "important");
        host.innerHTML = "";
        host.appendChild(svg);
        continue;
      }
      const normalizedPlant =
        plantSvg instanceof SVGElement ? plantSvg : replacePlantUmlImageWithInlineSvgForPdf(plantImg);
      if (normalizedPlant instanceof SVGElement) {
        normalizePlantUmlInlineSvgForPdf(normalizedPlant);
        host.innerHTML = "";
        host.appendChild(normalizedPlant);
      }
    }

    for (const viewport of Array.from(document.querySelectorAll(".mdexplore-mermaid-viewport"))) {
      if (!(viewport instanceof HTMLElement)) {
        continue;
      }
      viewport.scrollLeft = 0;
      viewport.scrollTop = 0;
      viewport.style.setProperty("overflow", "hidden", "important");
      viewport.style.setProperty("scrollbar-width", "none", "important");
      viewport.style.setProperty("-ms-overflow-style", "none", "important");
    }

    for (const img of Array.from(document.querySelectorAll("img.plantuml"))) {
      if (!(img instanceof HTMLImageElement)) {
        continue;
      }
      replacePlantUmlImageWithInlineSvgForPdf(img);
    }

    for (const svg of Array.from(document.querySelectorAll("svg.mdexplore-plantuml-inline"))) {
      normalizePlantUmlInlineSvgForPdf(svg);
    }

    for (const svg of Array.from(document.querySelectorAll(".mermaid svg"))) {
      if (!(svg instanceof SVGElement)) {
        continue;
      }
      svg.style.removeProperty("transform");
      svg.removeAttribute("width");
      svg.removeAttribute("height");
      svg.style.removeProperty("width");
      svg.style.removeProperty("max-width");
      svg.style.removeProperty("height");
      svg.style.setProperty("display", "block", "important");
      svg.style.setProperty("width", "var(--mdexplore-print-diagram-width, auto)", "important");
      svg.style.setProperty("max-width", "var(--mdexplore-print-diagram-max-width, 100%)", "important");
      svg.style.setProperty("height", "var(--mdexplore-print-diagram-height, auto)", "important");
      svg.style.setProperty("max-height", "var(--mdexplore-print-diagram-max-height, none)", "important");
    }

    // Expand regular markdown raster images to full printable content width.
    for (const img of Array.from(document.querySelectorAll("main img"))) {
      if (!(img instanceof HTMLImageElement)) {
        continue;
      }
      if (img.classList.contains("plantuml")) {
        continue;
      }
      if (img.closest(".mermaid")) {
        continue;
      }
      img.style.removeProperty("transform");
      img.style.removeProperty("width");
      img.style.setProperty("display", "block", "important");
      img.style.setProperty("width", "auto", "important");
      img.style.setProperty("max-width", "100%", "important");
      img.style.setProperty("height", "auto", "important");
      img.style.setProperty("object-fit", "contain", "important");
    }

    // Prevent horizontal-scroll snapshots in PDF for long command/code lines.
    for (const preNode of Array.from(document.querySelectorAll("pre"))) {
      if (!(preNode instanceof HTMLElement)) {
        continue;
      }
      preNode.style.setProperty("overflow", "visible", "important");
      preNode.style.setProperty("max-width", "100%", "important");
      preNode.style.setProperty("white-space", "pre-wrap", "important");
      preNode.style.setProperty("overflow-wrap", "anywhere", "important");
      preNode.style.setProperty("word-break", "break-word", "important");
    }
    for (const codeNode of Array.from(document.querySelectorAll("pre code, code[class*='language-']"))) {
      if (!(codeNode instanceof HTMLElement)) {
        continue;
      }
      codeNode.style.setProperty("white-space", "pre-wrap", "important");
      codeNode.style.setProperty("overflow-wrap", "anywhere", "important");
      codeNode.style.setProperty("word-break", "break-word", "important");
    }
  };

    const forceMermaidSvgMonochromeForPdf = (svgNode, options = null) => {
      if (!(svgNode instanceof SVGElement)) {
        return;
      }
      const TEXT_DARK = "#1a1a1a";
    const isSequenceDiagram = !!(options && typeof options === "object" && options.isSequence === true);
    const TRANSPARENT_VALUES = new Set(["none", "transparent", "rgba(0, 0, 0, 0)", "rgba(0,0,0,0)"]);
    const textTags = new Set(["text", "tspan"]);
    const paintableSelector = "path, line, polyline, polygon, rect, circle, ellipse, text, tspan, g, stop, marker";
    const clampByte = (value) => Math.max(0, Math.min(255, Math.round(value)));
    const parseRgbaText = (raw) => {
      const text = String(raw || "").trim().toLowerCase();
      const rgbMatch = text.match(/^rgba?\\(([^)]+)\\)$/);
      if (!(rgbMatch && rgbMatch[1])) {
        return null;
      }
      const parts = rgbMatch[1]
        .split(",")
        .map((part) => Number.parseFloat(String(part).trim()))
        .filter((part) => Number.isFinite(part));
      if (parts.length < 3) {
        return null;
      }
      return {
        r: clampByte(parts[0]),
        g: clampByte(parts[1]),
        b: clampByte(parts[2]),
        a: parts.length >= 4 ? Math.max(0, Math.min(1, parts[3])) : 1,
      };
    };
    const parseColorToRgba = (value) => {
      const raw = String(value || "").trim().toLowerCase();
      if (!raw || TRANSPARENT_VALUES.has(raw) || raw.startsWith("url(")) {
        return null;
      }
      const rgbaDirect = parseRgbaText(raw);
      if (rgbaDirect) {
        return rgbaDirect;
      }
      const hex = raw.startsWith("#") ? raw.slice(1) : "";
      if (hex.length === 3 || hex.length === 4) {
        const r = parseInt(hex[0] + hex[0], 16);
        const g = parseInt(hex[1] + hex[1], 16);
        const b = parseInt(hex[2] + hex[2], 16);
        const a = hex.length === 4 ? parseInt(hex[3] + hex[3], 16) / 255 : 1;
        if ([r, g, b, a].every((v) => Number.isFinite(v))) {
          return { r, g, b, a };
        }
      }
      if (hex.length === 6 || hex.length === 8) {
        const r = parseInt(hex.slice(0, 2), 16);
        const g = parseInt(hex.slice(2, 4), 16);
        const b = parseInt(hex.slice(4, 6), 16);
        const a = hex.length === 8 ? parseInt(hex.slice(6, 8), 16) / 255 : 1;
        if ([r, g, b, a].every((v) => Number.isFinite(v))) {
          return { r, g, b, a };
        }
      }
      // Fallback to browser color parser for color functions we don't parse.
      try {
        if (!window.__mdexploreColorProbeEl || !(window.__mdexploreColorProbeEl instanceof HTMLElement)) {
          const probe = document.createElement("span");
          probe.style.position = "absolute";
          probe.style.left = "-10000px";
          probe.style.top = "-10000px";
          probe.style.visibility = "hidden";
          probe.style.pointerEvents = "none";
          probe.textContent = ".";
          document.body.appendChild(probe);
          window.__mdexploreColorProbeEl = probe;
        }
        const probe = window.__mdexploreColorProbeEl;
        probe.style.color = raw;
        const resolved = window.getComputedStyle(probe).color;
        const rgbaResolved = parseRgbaText(resolved);
        if (rgbaResolved) {
          return rgbaResolved;
        }
      } catch (_error) {
        // Ignore parser fallback failures and use static fallback gray.
      }
      return null;
    };
    const rgbToLuma = (r, g, b) => (0.2126 * r) + (0.7152 * g) + (0.0722 * b);
    const rgbSaturation = (r, g, b) => {
      const maxV = Math.max(r, g, b);
      const minV = Math.min(r, g, b);
      if (maxV <= 0.0001) {
        return 0;
      }
      return (maxV - minV) / maxV;
    };
    const grayRgbFromSource = (sourceColor, grayMin, grayMax, fallbackGray) => {
      const parsed = parseColorToRgba(sourceColor);
      if (!parsed || parsed.a <= 0.001) {
        const f = clampByte(fallbackGray);
        return `rgb(${f}, ${f}, ${f})`;
      }
      const luma = rgbToLuma(parsed.r, parsed.g, parsed.b);
      // Slightly lower high-saturation colors so colored fills with similar
      // luminance don't collapse into the same gray band.
      const sat = rgbSaturation(parsed.r, parsed.g, parsed.b);
      const adjustedLuma = Math.max(0, Math.min(255, luma - (sat * 26)));
      const mapped = clampByte(grayMin + ((grayMax - grayMin) * (adjustedLuma / 255)));
      return `rgb(${mapped}, ${mapped}, ${mapped})`;
    };
    const colorIsTransparent = (value) => {
      const normalized = String(value || "").trim().toLowerCase();
      return !normalized || TRANSPARENT_VALUES.has(normalized);
    };
    const lightenTowardWhite = (colorText, ratio = 0.75, fallback = 240) => {
      const parsed = parseColorToRgba(colorText);
      if (!parsed || parsed.a <= 0.001) {
        const f = clampByte(fallback);
        return `rgb(${f}, ${f}, ${f})`;
      }
      const t = Math.max(0, Math.min(1, Number(ratio)));
      const r = clampByte(parsed.r + ((255 - parsed.r) * t));
      const g = clampByte(parsed.g + ((255 - parsed.g) * t));
      const b = clampByte(parsed.b + ((255 - parsed.b) * t));
      return `rgb(${r}, ${g}, ${b})`;
    };
    const resolveSvgBounds = () => {
      const vb = String(svgNode.getAttribute("viewBox") || "").trim();
      if (vb) {
        const parts = vb.split(/[\\s,]+/).map((part) => Number.parseFloat(part));
        if (parts.length === 4 && parts.every((part) => Number.isFinite(part))) {
          return { x: parts[0], y: parts[1], width: Math.abs(parts[2]), height: Math.abs(parts[3]) };
        }
      }
      try {
        const bbox = svgNode.getBBox();
        if (bbox && Number.isFinite(bbox.width) && Number.isFinite(bbox.height) && bbox.width > 0 && bbox.height > 0) {
          return { x: bbox.x, y: bbox.y, width: bbox.width, height: bbox.height };
        }
      } catch (_error) {
        // Ignore and use fallback below.
      }
      return null;
    };
    const isFullDiagramBackground = (node, svgBounds) => {
      if (!(node instanceof SVGElement) || !svgBounds) {
        return false;
      }
      const computed = window.getComputedStyle(node);
      if (colorIsTransparent(computed.fill || "")) {
        return false;
      }
      let bbox = null;
      try {
        bbox = node.getBBox();
      } catch (_error) {
        bbox = null;
      }
      if (!bbox || bbox.width <= 0 || bbox.height <= 0) {
        return false;
      }

      const margin = Math.max(3, Math.min(svgBounds.width, svgBounds.height) * 0.012);
      const touchesLeft = bbox.x <= (svgBounds.x + margin);
      const touchesTop = bbox.y <= (svgBounds.y + margin);
      const touchesRight = (bbox.x + bbox.width) >= (svgBounds.x + svgBounds.width - margin);
      const touchesBottom = (bbox.y + bbox.height) >= (svgBounds.y + svgBounds.height - margin);
      const coversWidth = bbox.width >= (svgBounds.width * 0.92);
      const coversHeight = bbox.height >= (svgBounds.height * 0.92);
      return touchesLeft && touchesTop && touchesRight && touchesBottom && coversWidth && coversHeight;
    };

    const tightenSvgCanvasToContent = () => {
      let currentViewBox = null;
      const vbText = String(svgNode.getAttribute("viewBox") || "").trim();
      if (vbText) {
        const parts = vbText
          .split(/[\\s,]+/)
          .map((part) => Number.parseFloat(part))
          .filter((part) => Number.isFinite(part));
        if (parts.length === 4 && parts[2] > 1 && parts[3] > 1) {
          currentViewBox = { x: parts[0], y: parts[1], width: parts[2], height: parts[3] };
        }
      }
      let bbox = null;
      try {
        bbox = svgNode.getBBox();
      } catch (_error) {
        bbox = null;
      }
      if (!bbox || bbox.width <= 1 || bbox.height <= 1) {
        return;
      }
      const widthGain = currentViewBox ? (currentViewBox.width / Math.max(1, bbox.width)) : 1;
      const heightGain = currentViewBox ? (currentViewBox.height / Math.max(1, bbox.height)) : 1;
      if (widthGain < 1.02 && heightGain < 1.02) {
        return;
      }
      // Generic crop for all Mermaid diagrams in PDF mode with a small cushion.
      // Sequence diagrams keep a bit more room for arrow heads/labels.
      const padXRatio = isSequenceDiagram ? 0.05 : 0.028;
      const padYRatio = isSequenceDiagram ? 0.055 : 0.034;
      const padX = Math.max(7, bbox.width * padXRatio);
      const padY = Math.max(7, bbox.height * padYRatio);
      svgNode.setAttribute(
        "viewBox",
        `${bbox.x - padX} ${bbox.y - padY} ${bbox.width + (2 * padX)} ${bbox.height + (2 * padY)}`
      );
      svgNode.removeAttribute("width");
      svgNode.removeAttribute("height");
      svgNode.style.removeProperty("width");
      svgNode.style.removeProperty("max-width");
      svgNode.style.removeProperty("height");
    };

    // PDF must not inherit GUI viewport assumptions; re-fit canvas to content.
    tightenSvgCanvasToContent();

    svgNode.style.setProperty("background", "#ffffff", "important");
    svgNode.style.setProperty("color", TEXT_DARK, "important");
    svgNode.style.removeProperty("filter");
    svgNode.style.removeProperty("-webkit-filter");

    for (const node of Array.from(svgNode.querySelectorAll(paintableSelector))) {
      if (!(node instanceof SVGElement)) {
        continue;
      }
      const tag = String(node.tagName || "").toLowerCase();
      const computed = window.getComputedStyle(node);
      const computedFill = String(computed.fill || "").trim();
      const computedStroke = String(computed.stroke || "").trim();

      if (tag === "stop") {
        const stopGray = grayRgbFromSource(computed.stopColor || computedFill, 125, 246, 212);
        node.style.setProperty("stop-color", stopGray, "important");
        node.style.setProperty("stop-opacity", "1", "important");
        continue;
      }

      if (textTags.has(tag)) {
        // PDF monochrome mode keeps Mermaid text consistently dark.
        node.style.setProperty("fill", TEXT_DARK, "important");
        node.style.setProperty("stroke", "none", "important");
        node.style.setProperty("color", TEXT_DARK, "important");
        node.style.setProperty("opacity", "1", "important");
        continue;
      }

      if (!colorIsTransparent(computedFill)) {
        const inLabel = !!node.closest(".edgeLabel, .labelBkg, .messageText");
        const fillGray = inLabel
          ? grayRgbFromSource(computedFill, 204, 250, 234)
          : grayRgbFromSource(computedFill, 88, 242, 206);
        node.style.setProperty("fill", fillGray, "important");
        node.style.setProperty("fill-opacity", "1", "important");
      } else if (node.hasAttribute("fill")) {
        node.style.setProperty("fill", "none", "important");
      }

      if (!colorIsTransparent(computedStroke)) {
        const strokeGray = grayRgbFromSource(computedStroke, 28, 168, 96);
        node.style.setProperty("stroke", strokeGray, "important");
        node.style.setProperty("stroke-opacity", "1", "important");
      } else if (node.hasAttribute("stroke")) {
        node.style.setProperty("stroke", "none", "important");
      }
      node.style.setProperty("opacity", "1", "important");
    }

    // Some Mermaid renderers emit labels via foreignObject HTML instead of
    // pure SVG text nodes. Force readable print colors there as well.
    for (const foreign of Array.from(svgNode.querySelectorAll("foreignObject"))) {
      if (!(foreign instanceof SVGElement)) {
        continue;
      }
      foreign.style.setProperty("color", TEXT_DARK, "important");
      foreign.style.setProperty("opacity", "1", "important");
      const htmlLabels = Array.from(foreign.querySelectorAll("*"));
      for (const element of htmlLabels) {
        if (!(element instanceof HTMLElement)) {
          continue;
        }
        element.style.setProperty("color", TEXT_DARK, "important");
        element.style.setProperty("fill", TEXT_DARK, "important");
        // Keep fills transparent so grayscale shape treatment remains visible.
        element.style.setProperty("background", "transparent", "important");
        element.style.setProperty("border-color", "rgb(96, 96, 96)", "important");
      }
    }

    // If a Mermaid diagram has an edge-to-edge shaded background panel,
    // lighten that panel strongly (~75% toward white) to reduce page tint.
    const svgBounds = resolveSvgBounds();
    const backgroundCandidates = Array.from(
      svgNode.querySelectorAll("rect, path, polygon, circle, ellipse")
    );
    for (const node of backgroundCandidates) {
      if (!(node instanceof SVGElement)) {
        continue;
      }
      if (!isFullDiagramBackground(node, svgBounds)) {
        continue;
      }
      const computed = window.getComputedStyle(node);
      const lighterFill = lightenTowardWhite(computed.fill || node.getAttribute("fill") || "", 0.75, 244);
      node.style.setProperty("fill", lighterFill, "important");
      node.style.setProperty("fill-opacity", "1", "important");
    }
  };

  const forceAllMermaidMonochromeForPdf = () => {
    for (const block of Array.from(document.querySelectorAll(".mermaid"))) {
      if (!(block instanceof HTMLElement)) {
        continue;
      }
      const sourceText = String(
        (block.dataset && block.dataset.mdexploreMermaidSource) ||
          block.getAttribute("data-mdexplore-mermaid-source") ||
          "",
      );
      const explicitKind = String((block.dataset && block.dataset.mdexploreMermaidKind) || "")
        .trim()
        .toLowerCase();
      const detectedKind =
        explicitKind ||
        (typeof window.__mdexploreDetectMermaidKind === "function"
          ? String(window.__mdexploreDetectMermaidKind(sourceText) || "").toLowerCase()
          : "");
      const isSequenceDiagram =
        detectedKind === "sequence" || /^\\s*sequenceDiagram\\b/im.test(sourceText);
      const svg = block.querySelector("svg");
      if (svg instanceof SVGElement) {
        forceMermaidSvgMonochromeForPdf(svg, { isSequence: isSequenceDiagram });
      }
    }
  };

  const startPdfMermaidCleanRender = (forceRender = false) => {
    const mermaidBlocks = Array.from(document.querySelectorAll(".mermaid")).filter(
      (block) => block instanceof HTMLElement
    );
    const backend = String(window.__mdexploreMermaidBackend || "js").toLowerCase();
    if (backend === "rust") {
      if (window.__mdexplorePdfMermaidInFlight) {
        return;
      }
      window.__mdexplorePdfMermaidInFlight = true;
      window.__mdexplorePdfMermaidReady = false;
      window.__mdexplorePdfMermaidError = "";
      try {
        // Rust PDF mode uses the dedicated PDF SVG cache produced by Python
        // with default mmdr theming (no GUI post-processing).
        const cacheByMode = window.__mdexploreMermaidSvgCacheByMode;
        if (!cacheByMode || typeof cacheByMode !== "object") {
          window.__mdexploreMermaidSvgCacheByMode = {};
        }
        if (
          !window.__mdexploreMermaidSvgCacheByMode.auto ||
          typeof window.__mdexploreMermaidSvgCacheByMode.auto !== "object"
        ) {
          window.__mdexploreMermaidSvgCacheByMode.auto = {};
        }
        if (
          !window.__mdexploreMermaidSvgCacheByMode.pdf ||
          typeof window.__mdexploreMermaidSvgCacheByMode.pdf !== "object"
        ) {
          window.__mdexploreMermaidSvgCacheByMode.pdf = {};
        }
        const autoCache = window.__mdexploreMermaidSvgCacheByMode.auto;
        const pdfCache =
          window.__mdexploreMermaidSvgCacheByMode.pdf &&
          typeof window.__mdexploreMermaidSvgCacheByMode.pdf === "object"
            ? window.__mdexploreMermaidSvgCacheByMode.pdf
            : null;
        let missingCount = 0;
        for (const block of mermaidBlocks) {
          if (!(block instanceof HTMLElement)) {
            continue;
          }
          const hashKey = String(block.getAttribute("data-mdexplore-mermaid-hash") || "").trim().toLowerCase();
          if (hashKey) {
            const existingSvg = block.querySelector("svg");
            if (
              existingSvg instanceof SVGElement &&
              typeof existingSvg.outerHTML === "string" &&
              existingSvg.outerHTML.indexOf("<svg") >= 0 &&
              typeof autoCache[hashKey] !== "string"
            ) {
              // Snapshot preview SVG before replacing with PDF variant so
              // post-export restore can reliably return to GUI styling.
              autoCache[hashKey] = existingSvg.outerHTML;
            }
          }
          const cachedSvg = hashKey && pdfCache && typeof pdfCache[hashKey] === "string" ? pdfCache[hashKey] : "";
          if (cachedSvg && cachedSvg.indexOf("<svg") >= 0) {
            block.removeAttribute("data-mdexplore-mermaid-render");
            block.classList.remove("mermaid-pending", "mermaid-error", "mermaid-rust-fallback");
            block.classList.add("mermaid-ready");
            block.innerHTML = cachedSvg;
            continue;
          }
          const existingSvg = block.querySelector("svg");
          if (existingSvg instanceof SVGElement) {
            block.removeAttribute("data-mdexplore-mermaid-render");
            block.classList.remove("mermaid-pending", "mermaid-error", "mermaid-rust-fallback");
            block.classList.add("mermaid-ready");
            continue;
          }
          missingCount += 1;
          const rustError = (block.getAttribute("data-mdexplore-rust-error") || "").trim();
          block.removeAttribute("data-mdexplore-mermaid-render");
          block.classList.remove("mermaid-pending", "mermaid-ready", "mermaid-rust-fallback");
          block.classList.add("mermaid-error");
          block.textContent = rustError
            ? `Mermaid render failed: Rust renderer: ${rustError}`
            : "Mermaid render failed: Rust PDF SVG unavailable";
        }
        if (missingCount > 0) {
          window.__mdexplorePdfMermaidError = `${missingCount} Rust Mermaid block(s) missing cached PDF SVG`;
        }
        window.__mdexploreMermaidReady = true;
        window.__mdexploreMermaidPaletteMode = "pdf";
      } catch (error) {
        window.__mdexplorePdfMermaidError =
          error && error.message ? error.message : String(error || "Rust PDF Mermaid render failed");
        window.__mdexploreMermaidReady = false;
      } finally {
        window.__mdexplorePdfMermaidInFlight = false;
        window.__mdexplorePdfMermaidReady = true;
      }
      return;
    }
    if (mermaidBlocks.length === 0) {
      window.__mdexplorePdfMermaidReady = true;
      window.__mdexploreMermaidReady = true;
      window.__mdexploreMermaidPaletteMode = "pdf";
      return;
    }
    if (!forceRender && window.__mdexplorePdfMermaidReady && !window.__mdexplorePdfMermaidInFlight) {
      return;
    }
    if (window.__mdexplorePdfMermaidInFlight) {
      return;
    }
    window.__mdexplorePdfMermaidInFlight = true;
    window.__mdexplorePdfMermaidReady = false;
    window.__mdexplorePdfMermaidError = "";

    const normalizeMermaidSource = (value) => String(value || "").replace(/\\r\\n/g, "\\n").trim();

    (async () => {
      try {
        if (!window.__mdexploreLoadMermaidScript) {
          throw new Error("Mermaid loader unavailable in preview page");
        }
        const loaded = await window.__mdexploreLoadMermaidScript();
        if (!loaded || !window.mermaid) {
          throw new Error("Mermaid script failed to load for PDF render");
        }
        const config =
          (window.__mdexploreMermaidInitConfig && window.__mdexploreMermaidInitConfig("pdf")) || {
            startOnLoad: false,
            securityLevel: "loose",
            theme: "default",
            darkMode: false,
          };
        mermaid.initialize(config);

        let renderFailures = 0;
        for (let index = 0; index < mermaidBlocks.length; index += 1) {
          const block = mermaidBlocks[index];
          if (!(block instanceof HTMLElement)) {
            continue;
          }
          let sourceText = normalizeMermaidSource(block.dataset && block.dataset.mdexploreMermaidSource);
          if (!sourceText) {
            const hasRenderedDiagram = !!block.querySelector("svg");
            if (!hasRenderedDiagram) {
              sourceText = normalizeMermaidSource(block.textContent || "");
            }
            if (sourceText) {
              block.dataset.mdexploreMermaidSource = sourceText;
            }
          }
          if (!sourceText) {
            renderFailures += 1;
            block.classList.remove("mermaid-pending", "mermaid-ready");
            block.classList.add("mermaid-error");
            block.textContent = "Mermaid source unavailable for PDF render";
            continue;
          }
          block.classList.remove("mermaid-ready", "mermaid-error");
          block.classList.add("mermaid-pending");
          block.textContent = "Mermaid rendering...";
          try {
            const renderId = `mdexplore_pdf_mermaid_${Date.now()}_${index}`;
            const renderResult = await mermaid.render(renderId, sourceText);
            const svgMarkup =
              renderResult && typeof renderResult === "object" && typeof renderResult.svg === "string"
                ? renderResult.svg
                : String(renderResult || "");
            if (!svgMarkup || svgMarkup.indexOf("<svg") < 0) {
              throw new Error("Mermaid returned empty SVG for PDF render");
            }
            block.innerHTML = svgMarkup;
            const renderedSvg = block.querySelector("svg");
            forceMermaidSvgMonochromeForPdf(renderedSvg);
            block.classList.remove("mermaid-pending", "mermaid-error");
            block.classList.add("mermaid-ready");
          } catch (renderError) {
            renderFailures += 1;
            block.classList.remove("mermaid-pending", "mermaid-ready");
            block.classList.add("mermaid-error");
            const message =
              renderError && renderError.message ? renderError.message : String(renderError || "Unknown Mermaid error");
            block.textContent = `Mermaid render failed: ${message}`;
          }
        }

        window.__mdexploreMermaidReady = true;
        window.__mdexploreMermaidPaletteMode = "pdf";
        if (renderFailures > 0) {
          window.__mdexplorePdfMermaidError = `${renderFailures} Mermaid block(s) failed during PDF clean render`;
        }
      } catch (error) {
        window.__mdexplorePdfMermaidError = error && error.message ? error.message : String(error);
        window.__mdexploreMermaidReady = false;
      } finally {
        window.__mdexplorePdfMermaidReady = true;
        window.__mdexplorePdfMermaidInFlight = false;
      }
    })();
  };

  if (__MDEXPLORE_RESET_MERMAID__) {
    window.__mdexploreMermaidReady = false;
    window.__mdexploreMermaidPaletteMode = "";
    window.__mdexplorePdfMermaidReady = false;
    window.__mdexplorePdfMermaidInFlight = false;
    window.__mdexplorePdfMermaidError = "";
  }
  startPdfMermaidCleanRender(__MDEXPLORE_FORCE_MERMAID__);
  if (window.__mdexploreTryTypesetMath) {
    window.__mdexploreTryTypesetMath();
  }
  if (window.__mdexploreApplyPlantUmlZoomControls) {
    window.__mdexploreApplyPlantUmlZoomControls("pdf");
  }
  normalizeDiagramStateForPdf();
  // Apply print-safe grayscale for both Mermaid backends. Rust still uses the
  // dedicated PDF SVG source; this pass only normalizes print contrast.
  forceAllMermaidMonochromeForPdf();
  // Ensure interactive zoom/pan toolbars never appear in PDF snapshots.
  for (const toolbar of Array.from(document.querySelectorAll(".mdexplore-mermaid-toolbar"))) {
    if (!(toolbar instanceof HTMLElement)) {
      continue;
    }
    toolbar.dataset.mdexplorePdfHidden = "1";
    toolbar.style.setProperty("display", "none", "important");
  }
  // Hide diagram viewport scrollbars for PDF output.
  for (const viewport of Array.from(document.querySelectorAll(".mdexplore-mermaid-viewport"))) {
    if (!(viewport instanceof HTMLElement)) {
      continue;
    }
    viewport.dataset.mdexplorePdfViewportHidden = "1";
    viewport.style.setProperty("overflow", "hidden", "important");
    viewport.style.setProperty("scrollbar-width", "none", "important");
    viewport.style.setProperty("-ms-overflow-style", "none", "important");
    viewport.scrollLeft = 0;
    viewport.scrollTop = 0;
  }

  // Decide how each diagram section should paginate for PDF output. This pass
  // is the bridge between DOM content and the later Qt print snapshot: it
  // classifies sections as portrait/landscape and keep/spill, moves heading
  // clusters into diagram fences so they paginate as one unit, and records the
  // resulting layout hints for footer stamping.
  const markDiagramPrintLayout = () => {
    const PRINT_LAYOUT_KNOBS = __MDEXPLORE_PRINT_LAYOUT_KNOBS__;
    const HEADING_TO_DIAGRAM_GAP_PX = PRINT_LAYOUT_KNOBS.headingToDiagramGapPx;
    const PRINT_LAYOUT_SAFETY_PX = PRINT_LAYOUT_KNOBS.layoutSafetyPx;
    // PDF Mermaid shrink floor for one-page fit decisions. This is
    // intentionally user-tweakable and controls when tall flow/activity
    // diagrams are allowed to stay on one page instead of spilling.
    const MIN_PRINT_DIAGRAM_FONT_PT = PRINT_LAYOUT_KNOBS.minPrintDiagramFontPt;
    const minPrintDiagramFontPx = MIN_PRINT_DIAGRAM_FONT_PT * (4 / 3);
    const maxPrintDiagramFontPx = PRINT_LAYOUT_KNOBS.maxPrintDiagramFontPt * (4 / 3);
    // PDF page selection must be based on print-page geometry, not the live
    // GUI viewport. The export target is US Letter, so use Letter CSS-pixel
    // dimensions here; otherwise the keep/landscape classifier makes the wrong
    // tradeoffs for wide diagrams and heading orphan control.
    const letterPortraitWidthPx = PRINT_LAYOUT_KNOBS.portraitLetterWidthPx;
    const letterPortraitHeightPx = PRINT_LAYOUT_KNOBS.portraitLetterHeightPx;
    const letterLandscapeWidthPx = PRINT_LAYOUT_KNOBS.landscapeLetterWidthPx;
    const letterLandscapeHeightPx = PRINT_LAYOUT_KNOBS.landscapeLetterHeightPx;
    const printableWidthPortrait = Math.max(
      PRINT_LAYOUT_KNOBS.portraitMinWidthPx,
      letterPortraitWidthPx - PRINT_LAYOUT_KNOBS.horizontalMarginPx,
    );
    const printableHeightPortrait = Math.max(
      PRINT_LAYOUT_KNOBS.portraitMinHeightPx,
      letterPortraitHeightPx - PRINT_LAYOUT_KNOBS.verticalMarginPx,
    );
    const printableWidthLandscape = Math.max(
      PRINT_LAYOUT_KNOBS.landscapeMinWidthPx,
      letterLandscapeWidthPx - PRINT_LAYOUT_KNOBS.horizontalMarginPx,
    );
    const printableHeightLandscape = Math.max(
      PRINT_LAYOUT_KNOBS.landscapeMinHeightPx,
      letterLandscapeHeightPx - PRINT_LAYOUT_KNOBS.verticalMarginPx,
    );
    let diagramCount = 0;
    let keepCount = 0;
    let allowBreakCount = 0;
    let landscapeCount = 0;
    const landscapeHeadings = [];
    const diagramHeadings = [];

    // Reset any previous preflight wrappers before recomputing layout. PDF
    // export retries can run this block more than once.
    const unwrapPrintBlocks = () => {
      for (const block of Array.from(document.querySelectorAll(".mdexplore-print-block[data-mdexplore-print-block='1']"))) {
        if (!(block instanceof HTMLElement)) {
          continue;
        }
        const parent = block.parentNode;
        if (!parent) {
          continue;
        }
        while (block.firstChild) {
          parent.insertBefore(block.firstChild, block);
        }
        parent.removeChild(block);
      }
    };

    const parseLength = (value) => {
      const num = Number.parseFloat(String(value || "").replace(/px$/i, "").trim());
      return Number.isFinite(num) ? num : 0;
    };

    const headingLevel = (node) => {
      if (!(node instanceof HTMLElement)) {
        return 0;
      }
      const match = String(node.tagName || "").match(/^H([1-6])$/i);
      return match ? Number.parseInt(match[1], 10) : 0;
    };

    const previousMeaningfulElement = (node) => {
      let current = node ? node.previousSibling : null;
      while (current) {
        if (current instanceof HTMLElement) {
          return current;
        }
        if (current instanceof Text && String(current.textContent || "").trim()) {
          return null;
        }
        current = current.previousSibling;
      }
      return null;
    };

    const nextMeaningfulElement = (node) => {
      let current = node ? node.nextSibling : null;
      while (current) {
        if (current instanceof HTMLElement) {
          return current;
        }
        if (current instanceof Text && String(current.textContent || "").trim()) {
          return null;
        }
        current = current.nextSibling;
      }
      return null;
    };

    // Heading height is measured against an explicit printable width so orphan
    // control uses stable numbers instead of live viewport geometry.
    const stableHeadingHeight = (heading, widthPx) => {
      if (!(heading instanceof HTMLElement)) {
        return 0;
      }
      const restore = {
        display: heading.style.getPropertyValue("display"),
        width: heading.style.getPropertyValue("width"),
        maxWidth: heading.style.getPropertyValue("max-width"),
        boxSizing: heading.style.getPropertyValue("box-sizing"),
        whiteSpace: heading.style.getPropertyValue("white-space"),
      };
      heading.style.setProperty("display", "block", "important");
      if (widthPx > 0) {
        const widthText = `${Math.round(widthPx)}px`;
        heading.style.setProperty("width", widthText, "important");
        heading.style.setProperty("max-width", widthText, "important");
      }
      heading.style.setProperty("box-sizing", "border-box", "important");
      heading.style.setProperty("white-space", "normal", "important");
      const rect = heading.getBoundingClientRect();
      const computed = window.getComputedStyle(heading);
      const marginTop = parseLength(computed.marginTop);
      const marginBottom = parseLength(computed.marginBottom);
      const height = Math.max(0, rect.height + marginTop + marginBottom);
      if (restore.display) {
        heading.style.setProperty("display", restore.display);
      } else {
        heading.style.removeProperty("display");
      }
      if (restore.width) {
        heading.style.setProperty("width", restore.width);
      } else {
        heading.style.removeProperty("width");
      }
      if (restore.maxWidth) {
        heading.style.setProperty("max-width", restore.maxWidth);
      } else {
        heading.style.removeProperty("max-width");
      }
      if (restore.boxSizing) {
        heading.style.setProperty("box-sizing", restore.boxSizing);
      } else {
        heading.style.removeProperty("box-sizing");
      }
      if (restore.whiteSpace) {
        heading.style.setProperty("white-space", restore.whiteSpace);
      } else {
        heading.style.removeProperty("white-space");
      }
      return height;
    };

    const detectMermaidKindForFence = (fence) => {
      if (!(fence instanceof HTMLElement)) {
        return "";
      }
      const mermaid = fence.querySelector(".mermaid");
      if (!(mermaid instanceof HTMLElement)) {
        return "";
      }
      const explicitKind = String(mermaid.dataset.mdexploreMermaidKind || "")
        .trim()
        .toLowerCase();
      if (explicitKind) {
        return explicitKind;
      }
      const sourceText = String(mermaid.dataset.mdexploreMermaidSource || mermaid.textContent || "");
      if (/^\s*sequenceDiagram\b/im.test(sourceText)) {
        return "sequence";
      }
      if (/^\s*classDiagram\b/im.test(sourceText)) {
        return "class";
      }
      if (/^\s*erDiagram\b/im.test(sourceText)) {
        return "er";
      }
      if (/^\s*stateDiagram(?:-v2)?\b/im.test(sourceText)) {
        return "state";
      }
      if (/^\s*(?:graph|flowchart)\b/im.test(sourceText)) {
        return "flowchart";
      }
      return "";
    };

    // Diagram fit decisions operate on intrinsic SVG/image dimensions rather
    // than already-scaled CSS boxes so one-page and spill decisions are
    // reproducible.
    const intrinsicDiagramSize = (fence) => {
      if (!(fence instanceof HTMLElement)) {
        return { width: 0, height: 0 };
      }
      const svg = fence.querySelector("svg");
      if (svg instanceof SVGElement) {
        const viewBox = String(svg.getAttribute("viewBox") || "").trim();
        if (viewBox) {
          const parts = viewBox.split(/[\s,]+/).map((part) => Number.parseFloat(part));
          if (parts.length === 4 && parts.every((num) => Number.isFinite(num))) {
            const width = Math.abs(parts[2]);
            const height = Math.abs(parts[3]);
            if (width > 0 && height > 0) {
              return { width, height };
            }
          }
        }
        const width = parseLength(svg.getAttribute("width"));
        const height = parseLength(svg.getAttribute("height"));
        if (width > 0 && height > 0) {
          return { width, height };
        }
        try {
          const box = svg.getBBox();
          if (box && box.width > 0 && box.height > 0) {
            return { width: box.width, height: box.height };
          }
        } catch (_error) {
          // Ignore SVG bbox failures.
        }
      }
      const img = fence.querySelector("img.plantuml");
      if (img instanceof HTMLImageElement) {
        const width = Number(img.naturalWidth || 0);
        const height = Number(img.naturalHeight || 0);
        if (width > 0 && height > 0) {
          return { width, height };
        }
      }
      const rect = fence.getBoundingClientRect();
      return { width: Math.max(0, rect.width), height: Math.max(0, rect.height) };
    };

    // Font-size bounds drive the "shrink vs spill" decision. We cap at 12pt
    // on enlargement and compare against the configurable floor when deciding
    // whether a one-page shrink remains legible.
    const maxSvgFontPxForFence = (fence) => {
      if (!(fence instanceof HTMLElement)) {
        return 12;
      }
      let maxFontPx = 0;
      for (const node of Array.from(fence.querySelectorAll("svg text, svg tspan, svg foreignObject, svg foreignObject *"))) {
        if (!(node instanceof Element)) {
          continue;
        }
        const rawFont =
          node.getAttribute("font-size") ||
          (node instanceof HTMLElement || node instanceof SVGElement
            ? window.getComputedStyle(node).fontSize
            : "");
        const fontPx = parseLength(rawFont);
        if (fontPx > maxFontPx) {
          maxFontPx = fontPx;
        }
      }
      return Math.max(12, maxFontPx);
    };

    const collectHeadingClusterBeforeFence = (fence) => {
      const headings = [];
      let cursor = previousMeaningfulElement(fence);
      while (cursor instanceof HTMLElement) {
        const level = headingLevel(cursor);
        if (level <= 0) {
          break;
        }
        headings.unshift(cursor);
        cursor = previousMeaningfulElement(cursor);
      }
      return headings;
    };

    const clearFenceLayout = (fence) => {
      if (!(fence instanceof HTMLElement)) {
        return;
      }
      fence.classList.remove(
        "mdexplore-print-keep",
        "mdexplore-print-allow-break",
        "mdexplore-print-landscape-page",
        "mdexplore-print-with-heading",
        "mdexplore-print-break-before",
      );
      fence.style.removeProperty("--mdexplore-print-section-width");
      fence.style.removeProperty("--mdexplore-print-diagram-width");
      fence.style.removeProperty("--mdexplore-print-diagram-max-width");
      fence.style.removeProperty("--mdexplore-print-diagram-height");
      fence.style.removeProperty("--mdexplore-print-diagram-max-height");
      fence.style.removeProperty("--mdexplore-print-diagram-reserved-height");
      fence.style.removeProperty("width");
      fence.style.removeProperty("max-width");
      fence.style.removeProperty("min-height");
      for (const child of Array.from(fence.children)) {
        if (!(child instanceof HTMLElement)) {
          continue;
        }
        child.classList.remove(
          "mdexplore-print-heading-anchor",
          "mdexplore-print-heading-break-before",
          "mdexplore-print-heading-landscape",
        );
      }
    };

    const addSequenceBreakMarker = (fence) => {
      if (!(fence instanceof HTMLElement) || !fence.parentNode) {
        return;
      }
      const previousSibling = fence.previousSibling;
      const alreadyMarked =
        previousSibling instanceof HTMLElement &&
        previousSibling.classList.contains("mdexplore-print-sequence-page-break");
      if (alreadyMarked) {
        return;
      }
      const marker = document.createElement("div");
      marker.className = "mdexplore-print-sequence-page-break";
      fence.parentNode.insertBefore(marker, fence);
    };

    // Keep-together sections receive explicit width/height CSS variables so
    // the print snapshot path honors the same geometry this solver chose.
    const applyKeepSizing = (fence, sectionWidth, diagramWidth, diagramHeight, headingHeight) => {
      if (!(fence instanceof HTMLElement)) {
        return;
      }
      const widthText = `${Math.max(1, Math.round(diagramWidth))}px`;
      const heightText = `${Math.max(1, Math.round(diagramHeight))}px`;
      const sectionWidthText = `${Math.max(1, Math.round(sectionWidth))}px`;
      const reservedHeight = Math.max(1, Math.round(headingHeight + HEADING_TO_DIAGRAM_GAP_PX + diagramHeight));
      fence.style.setProperty("--mdexplore-print-section-width", sectionWidthText);
      fence.style.setProperty("--mdexplore-print-diagram-width", widthText);
      fence.style.setProperty("--mdexplore-print-diagram-max-width", widthText);
      fence.style.setProperty("--mdexplore-print-diagram-height", heightText);
      fence.style.setProperty("--mdexplore-print-diagram-max-height", heightText);
      fence.style.setProperty("--mdexplore-print-diagram-reserved-height", `${reservedHeight}px`);
    };

    // Spillable sections still get an explicit width budget, but height is left
    // unconstrained so Chromium can paginate through the diagram vertically.
    const applyBreakSizing = (fence, sectionWidth, diagramWidth) => {
      if (!(fence instanceof HTMLElement)) {
        return;
      }
      const widthText = `${Math.max(1, Math.round(diagramWidth))}px`;
      const sectionWidthText = `${Math.max(1, Math.round(sectionWidth))}px`;
      fence.style.setProperty("--mdexplore-print-section-width", sectionWidthText);
      fence.style.setProperty("--mdexplore-print-diagram-width", widthText);
      fence.style.setProperty("--mdexplore-print-diagram-max-width", widthText);
      fence.style.removeProperty("--mdexplore-print-diagram-height");
      fence.style.removeProperty("--mdexplore-print-diagram-max-height");
      fence.style.removeProperty("--mdexplore-print-diagram-reserved-height");
    };

    const remainingOnCurrentPage = (targetBlock, printableHeight) => {
      if (!(targetBlock instanceof HTMLElement)) {
        return printableHeight;
      }
      const contentRoot = document.querySelector("main") || document.body || document.documentElement;
      const contentTop =
        contentRoot instanceof HTMLElement
          ? contentRoot.getBoundingClientRect().top + window.scrollY
          : 0;
      const targetTop = targetBlock.getBoundingClientRect().top + window.scrollY;
      const relativeTop = Math.max(0, targetTop - contentTop);
      const pageOffset = relativeTop % Math.max(180, printableHeight);
      return {
        pageOffset,
        remaining: Math.max(0, printableHeight - pageOffset),
      };
    };

    unwrapPrintBlocks();
    for (const marker of Array.from(document.querySelectorAll(".mdexplore-print-sequence-page-break"))) {
      if (marker instanceof HTMLElement) {
        marker.remove();
      }
    }
    for (const fence of Array.from(document.querySelectorAll(".mdexplore-fence"))) {
      clearFenceLayout(fence);
    }

    for (const heading of Array.from(document.querySelectorAll("h1, h2, h3, h4, h5, h6"))) {
      if (!(heading instanceof HTMLElement)) {
        continue;
      }
      const parent = heading.parentElement;
      if (parent instanceof HTMLElement && parent.classList.contains("mdexplore-print-block")) {
        continue;
      }
      if (!heading.parentNode) {
        continue;
      }

      const level = headingLevel(heading);
      if (level <= 0 || level > 6) {
        continue;
      }
      if (heading.closest(".mdexplore-fence")) {
        continue;
      }

      const cluster = [heading];
      if (level <= 3) {
        let cursor = heading;
        while (true) {
          const next = nextMeaningfulElement(cursor);
          const nextLevel = headingLevel(next);
          if (
            !(next instanceof HTMLElement) ||
            next.parentNode !== heading.parentNode ||
            (next.parentElement instanceof HTMLElement &&
              next.parentElement.classList.contains("mdexplore-print-block")) ||
            nextLevel <= 0 ||
            nextLevel > 3
          ) {
            break;
          }
          cluster.push(next);
          cursor = next;
        }
      }

      const lastClusterItem = cluster[cluster.length - 1];
      const nextBlock = nextMeaningfulElement(lastClusterItem);
      if (
        nextBlock instanceof HTMLElement &&
        nextBlock.parentNode === heading.parentNode &&
        !(nextBlock.parentElement instanceof HTMLElement &&
          nextBlock.parentElement.classList.contains("mdexplore-print-block")) &&
        !nextBlock.classList.contains("mdexplore-fence") &&
        !/^H[1-6]$/.test(nextBlock.tagName)
      ) {
        cluster.push(nextBlock);
      }

      if (cluster.length <= 1) {
        continue;
      }

      const wrapper = document.createElement("div");
      wrapper.className = "mdexplore-print-block mdexplore-print-keep mdexplore-print-heading-keep";
      wrapper.dataset.mdexplorePrintBlock = "1";
      heading.parentNode.insertBefore(wrapper, heading);
      for (const element of cluster) {
        wrapper.appendChild(element);
      }
      for (const element of cluster) {
        if (/^H[1-6]$/.test(element.tagName)) {
          element.classList.add("mdexplore-print-heading-anchor");
        }
      }
    }

    for (const rule of Array.from(document.querySelectorAll("hr"))) {
      if (!(rule instanceof HTMLElement)) {
        continue;
      }
      const parent = rule.parentElement;
      if (parent instanceof HTMLElement && parent.classList.contains("mdexplore-print-block")) {
        continue;
      }
      if (!rule.parentNode) {
        continue;
      }
      const nextBlock = nextMeaningfulElement(rule);
      if (!(nextBlock instanceof HTMLElement)) {
        rule.classList.add("mdexplore-print-skip");
        continue;
      }
      const nextParent = nextBlock.parentElement;
      const nextWrapped =
        nextBlock.classList.contains("mdexplore-print-block") ||
        (nextParent instanceof HTMLElement && nextParent.classList.contains("mdexplore-print-block"));
      const nextIsBreakable =
        nextBlock.classList.contains("mdexplore-print-allow-break") ||
        nextBlock.classList.contains("mdexplore-print-landscape-page") ||
        !!nextBlock.querySelector(".mdexplore-print-allow-break, .mdexplore-print-landscape-page");
      if (nextIsBreakable) {
        rule.classList.add("mdexplore-print-skip");
        continue;
      }
      if (nextBlock.parentNode !== rule.parentNode && !nextWrapped) {
        rule.classList.add("mdexplore-print-skip");
        continue;
      }
      if (nextBlock.classList.contains("mdexplore-print-block")) {
        nextBlock.insertBefore(rule, nextBlock.firstChild);
        nextBlock.classList.add("mdexplore-print-keep", "mdexplore-print-heading-keep");
        continue;
      }
      const wrapper = document.createElement("div");
      wrapper.className = "mdexplore-print-block mdexplore-print-keep mdexplore-print-heading-keep";
      wrapper.dataset.mdexplorePrintBlock = "1";
      rule.parentNode.insertBefore(wrapper, rule);
      wrapper.appendChild(rule);
      wrapper.appendChild(nextBlock);
    }

    for (const fence of Array.from(document.querySelectorAll(".mdexplore-fence"))) {
      if (!(fence instanceof HTMLElement)) {
        continue;
      }
      const mermaid = fence.querySelector(".mermaid");
      const plantuml = fence.querySelector("img.plantuml, svg.mdexplore-plantuml-inline");
      const hasMermaid = mermaid instanceof HTMLElement;
      const hasPlantUml = plantuml instanceof Element;
      if (!hasMermaid && !hasPlantUml) {
        continue;
      }
      // Move any immediately-preceding heading cluster into the fence so the
      // pagination solver can treat "heading + diagram" as one print section.
      const headingCluster = collectHeadingClusterBeforeFence(fence);
      if (headingCluster.length > 0) {
        for (const heading of headingCluster) {
          fence.insertBefore(heading, fence.firstChild);
          heading.classList.add("mdexplore-print-heading-anchor");
        }
        fence.classList.add("mdexplore-print-with-heading");
      }

      const headingNodes = Array.from(fence.children).filter(
        (child) => child instanceof HTMLElement && headingLevel(child) > 0
      );
      const headingText = headingNodes.map((node) => String(node.textContent || "").trim()).filter(Boolean).join(" / ");
      if (headingText) {
        diagramHeadings.push(headingText);
      }

      const size = intrinsicDiagramSize(fence);
      if (size.width <= 0 || size.height <= 0) {
        continue;
      }

      const isSequenceMermaid = hasMermaid && detectMermaidKindForFence(fence) === "sequence";
      const aspectRatio = size.width / Math.max(1, size.height);
      const maxFontPx = maxSvgFontPxForFence(fence);
      const fontCapScale = maxFontPx > 0 ? (maxPrintDiagramFontPx / maxFontPx) : 1;

      const headingHeightPortrait = headingNodes.reduce(
        (sum, node) => sum + stableHeadingHeight(node, printableWidthPortrait),
        0,
      );
      const headingHeightLandscape = headingNodes.reduce(
        (sum, node) => sum + stableHeadingHeight(node, printableWidthLandscape),
        0,
      );

      const availableHeightPortrait = Math.max(
        PRINT_LAYOUT_KNOBS.keepMinHeightPx,
        printableHeightPortrait - headingHeightPortrait - HEADING_TO_DIAGRAM_GAP_PX - PRINT_LAYOUT_SAFETY_PX,
      );
      const availableHeightLandscape = Math.max(
        PRINT_LAYOUT_KNOBS.keepMinHeightPx,
        printableHeightLandscape - headingHeightLandscape - HEADING_TO_DIAGRAM_GAP_PX - PRINT_LAYOUT_SAFETY_PX,
      );

      const portraitScale = Math.min(
        printableWidthPortrait / size.width,
        availableHeightPortrait / size.height,
        fontCapScale,
      );
      const landscapeScale = Math.min(
        printableWidthLandscape / size.width,
        availableHeightLandscape / size.height,
        fontCapScale,
      );

      const portraitFontPx = portraitScale * maxFontPx;
      const landscapeFontPx = landscapeScale * maxFontPx;
      const canKeepPortrait = portraitScale > 0 && (maxFontPx <= 0 || portraitFontPx >= minPrintDiagramFontPx);
      const canKeepLandscape = landscapeScale > 0 && (maxFontPx <= 0 || landscapeFontPx >= minPrintDiagramFontPx);
      const wideLandscapeCandidate =
        aspectRatio >= PRINT_LAYOUT_KNOBS.wideDiagramAspectRatio &&
        landscapeScale > (portraitScale * PRINT_LAYOUT_KNOBS.wideDiagramLandscapeGain);

      // Landscape is only selected when it provides a meaningful improvement;
      // portrait should remain the default so later pages resume normal flow.
      let useLandscape = false;
      if (canKeepLandscape && (!canKeepPortrait || wideLandscapeCandidate)) {
        useLandscape = true;
      } else if (
        !canKeepPortrait &&
        hasPlantUml &&
        aspectRatio >= PRINT_LAYOUT_KNOBS.plantumlLandscapeAspectRatio &&
        landscapeScale > portraitScale
      ) {
        useLandscape = true;
      }

      const keepOnOnePage = useLandscape ? canKeepLandscape : (canKeepPortrait || (!useLandscape && canKeepLandscape));
      const chosenScale =
        keepOnOnePage
          ? (useLandscape ? landscapeScale : (canKeepPortrait ? portraitScale : landscapeScale))
          : Math.min(
              (useLandscape ? printableWidthLandscape : printableWidthPortrait) / size.width,
              fontCapScale,
            );
      const sectionWidth = useLandscape ? printableWidthLandscape : printableWidthPortrait;
      const chosenHeadingHeight = useLandscape ? headingHeightLandscape : headingHeightPortrait;
      const diagramWidth = Math.max(1, Math.round(size.width * chosenScale));
      const diagramHeight = Math.max(1, Math.round(size.height * chosenScale));

      if (useLandscape) {
        fence.classList.add("mdexplore-print-landscape-page");
        if (headingText) {
          landscapeHeadings.push(headingText);
        }
      }

      if (keepOnOnePage) {
        fence.classList.add("mdexplore-print-keep");
        applyKeepSizing(fence, sectionWidth, diagramWidth, diagramHeight, chosenHeadingHeight);
        keepCount += 1;
      } else {
        // Once the font floor is reached, preserve width and let Chromium spill
        // vertically rather than shrinking the diagram into illegibility.
        fence.classList.add("mdexplore-print-allow-break");
        applyBreakSizing(fence, sectionWidth, diagramWidth);
        allowBreakCount += 1;
      }

      const pageBudget = useLandscape ? printableHeightLandscape : printableHeightPortrait;
      const pageMetrics = remainingOnCurrentPage(fence, pageBudget);
      const projectedSectionHeight = chosenHeadingHeight + HEADING_TO_DIAGRAM_GAP_PX + diagramHeight;
      const shouldBreakBefore =
        pageMetrics.pageOffset > 1 &&
        (keepOnOnePage
          ? projectedSectionHeight > pageMetrics.remaining + 1
          : headingNodes.length > 0);
      if (shouldBreakBefore) {
        fence.classList.add("mdexplore-print-break-before");
        if (isSequenceMermaid) {
          addSequenceBreakMarker(fence);
        }
      }

      diagramCount += 1;
      if (useLandscape) {
        landscapeCount += 1;
      }
    }

    return {
      diagramCount,
      keepCount,
      allowBreakCount,
      landscapeCount,
      landscapeHeadings: Array.from(new Set(landscapeHeadings)),
      diagramHeadings: Array.from(new Set(diagramHeadings)),
    };
  };

  const diagramLayout = markDiagramPrintLayout();

  const landscapeTokenText = "__MDEXPLORE_LANDSCAPE_PAGE__";
  // Landscape decisions are passed back to Python via tiny hidden tokens so
  // the footer-stamping pass can rotate only those pages after printToPdf().
  for (const block of Array.from(document.querySelectorAll(".mdexplore-print-landscape-page"))) {
    if (!(block instanceof HTMLElement)) {
      continue;
    }
    let token = block.querySelector(":scope > .mdexplore-pdf-landscape-token");
    if (!(token instanceof HTMLElement)) {
      token = document.createElement("div");
      token.className = "mdexplore-pdf-landscape-token";
      token.textContent = landscapeTokenText;
      token.style.setProperty("display", "block", "important");
      token.style.setProperty("font-size", "2px", "important");
      token.style.setProperty("line-height", "2px", "important");
      token.style.setProperty("margin", "0", "important");
      token.style.setProperty("padding", "0", "important");
      token.style.setProperty("color", "#ffffff", "important");
      token.style.setProperty("pointer-events", "none", "important");
      block.insertBefore(token, block.firstChild);
    }
  }

  const hasMath = !!document.querySelector("mjx-container, .MathJax");
  const hasMermaid = !!document.querySelector(".mermaid");
  const plantumlImages = Array.from(document.querySelectorAll("img.plantuml"));
  const inlinePlantumlSvgs = Array.from(document.querySelectorAll("svg.mdexplore-plantuml-inline"));
  const hasPlantUml =
    plantumlImages.length > 0 || inlinePlantumlSvgs.length > 0 || !!document.querySelector(".plantuml-pending");
  const plantumlReady =
    !hasPlantUml ||
    (!!window.__mdexplorePdfPlantUmlReady) ||
    (
      !document.querySelector(".plantuml-pending") &&
      plantumlImages.every((img) => {
        if (!(img instanceof HTMLImageElement)) {
          return true;
        }
        return !!img.complete && Number(img.naturalWidth || 0) > 1 && Number(img.naturalHeight || 0) > 1;
      }) &&
      inlinePlantumlSvgs.every((svg) => svg instanceof SVGElement)
    );
  const mathReady = !hasMath || !!window.__mdexploreMathReady;
  const mermaidReady = !hasMermaid || !!window.__mdexplorePdfMermaidReady;
  const fontsReady = !document.fonts || document.fonts.status === "loaded";

  return { mathReady, mermaidReady, plantumlReady, fontsReady, hasMath, hasMermaid, hasPlantUml, diagramLayout };
})();
"""
        js = js.replace("__MDEXPLORE_FORCE_MERMAID__", "true" if attempt == 0 else "false")
        js = js.replace("__MDEXPLORE_RESET_MERMAID__", "true" if attempt == 0 else "false")
        # Keep PDF preflight policy sourced from Python constants so the
        # embedded JS remains a consumer of print-layout rules, not the owner.
        js = js.replace(
            "__MDEXPLORE_PRINT_LAYOUT_KNOBS__",
            json.dumps(_pdf_print_layout_knobs()),
        )
        self.preview.page().runJavaScript(
            js,
            lambda result, target=output_path, tries=attempt, key=source_key: self._on_pdf_precheck_result(
                target, tries, key, result
            ),
        )

    def _on_pdf_precheck_result(self, output_path: Path, attempt: int, source_key: str, result) -> None:
        """Continue waiting until print assets are ready, then trigger print."""
        math_ready = False
        mermaid_ready = False
        plantuml_ready = False
        fonts_ready = False
        if isinstance(result, dict):
            math_ready = bool(result.get("mathReady"))
            mermaid_ready = bool(result.get("mermaidReady"))
            plantuml_ready = bool(result.get("plantumlReady"))
            fonts_ready = bool(result.get("fontsReady"))
            diagram_layout = result.get("diagramLayout")
            if isinstance(diagram_layout, dict):
                self._pending_pdf_layout_hints = dict(diagram_layout)

        if math_ready and mermaid_ready and plantuml_ready and fonts_ready:
            self._trigger_pdf_print(output_path, source_key)
            return

        if attempt < PDF_EXPORT_PRECHECK_MAX_ATTEMPTS:
            if attempt == 0:
                self.statusBar().showMessage("Waiting for math/Mermaid/PlantUML/fonts before PDF export...")
            QTimer.singleShot(
                PDF_EXPORT_PRECHECK_INTERVAL_MS,
                lambda target=output_path, tries=attempt + 1, key=source_key: self._prepare_preview_for_pdf_export(
                    target, tries, key
                ),
            )
            return

        # Fall back instead of blocking export indefinitely if some assets never settle.
        self.statusBar().showMessage(
            "Proceeding with PDF export before all preview assets reported ready",
            3500,
        )
        self._trigger_pdf_print(output_path, source_key)

    def _trigger_pdf_print(self, output_path: Path, source_key: str) -> None:
        """Start Qt WebEngine PDF generation for the active preview page."""
        self.statusBar().showMessage(f"Rendering PDF snapshot: {output_path.name}...")
        preprint_js = """
(() => {
  const decodeSvgDataUriForPdf = (src) => {
    const raw = String(src || "");
    if (!raw.startsWith("data:image/svg+xml")) {
      return "";
    }
    const commaIndex = raw.indexOf(",");
    if (commaIndex < 0) {
      return "";
    }
    const meta = raw.slice(0, commaIndex).toLowerCase();
    const payload = raw.slice(commaIndex + 1);
    try {
      if (meta.includes(";base64")) {
        return atob(payload);
      }
      return decodeURIComponent(payload);
    } catch (_error) {
      return "";
    }
  };

  const intrinsicSvgSizeFromNodeForPdf = (svg) => {
    if (!(svg instanceof SVGElement)) {
      return { width: 0, height: 0 };
    }
    const viewBox = String(svg.getAttribute("viewBox") || "").trim();
    if (viewBox) {
      const parts = viewBox.split(/[\\s,]+/).map((part) => Number.parseFloat(part));
      if (parts.length === 4 && parts.every((num) => Number.isFinite(num))) {
        const width = Math.abs(parts[2]);
        const height = Math.abs(parts[3]);
        if (width > 0 && height > 0) {
          return { width, height };
        }
      }
    }
    const width = Number.parseFloat(String(svg.getAttribute("width") || "").replace(/px$/i, ""));
    const height = Number.parseFloat(String(svg.getAttribute("height") || "").replace(/px$/i, ""));
    if (Number.isFinite(width) && Number.isFinite(height) && width > 0 && height > 0) {
      return { width, height };
    }
    return { width: 0, height: 0 };
  };

  const normalizePlantUmlInlineSvgForPdf = (svg) => {
    if (!(svg instanceof SVGElement)) {
      return;
    }
    svg.classList.add("plantuml", "mdexplore-plantuml-inline");
    svg.style.removeProperty("transform");
    svg.style.setProperty("display", "block", "important");
    svg.style.setProperty("width", "var(--mdexplore-print-diagram-width, auto)", "important");
    svg.style.setProperty("max-width", "var(--mdexplore-print-diagram-max-width, 100%)", "important");
    svg.style.setProperty("height", "var(--mdexplore-print-diagram-height, auto)", "important");
    svg.style.setProperty("max-height", "var(--mdexplore-print-diagram-max-height, none)", "important");
    svg.style.setProperty("margin", "0 auto", "important");
  };

  const replacePlantUmlImageWithInlineSvgForPdf = (img) => {
    if (!(img instanceof HTMLImageElement)) {
      return null;
    }
    if (img.dataset.mdexplorePlantumlInline === "1") {
      return null;
    }
    const markup = decodeSvgDataUriForPdf(img.currentSrc || img.src || "");
    if (!markup) {
      return null;
    }
    try {
      const template = document.createElement("template");
      template.innerHTML = markup.trim();
      const svg = template.content.firstElementChild;
      if (!(svg instanceof SVGElement) || String(svg.tagName || "").toLowerCase() !== "svg") {
        return null;
      }
      const replacement = svg;
      replacement.setAttribute("data-mdexplore-original-img", img.outerHTML);
      replacement.setAttribute("data-mdexplorePlantumlInline", "1");
      replacement.dataset.mdexplorePlantumlInline = "1";
      normalizePlantUmlInlineSvgForPdf(replacement);
      img.replaceWith(replacement);
      return replacement;
    } catch (_error) {
      return null;
    }
  };

  if (document.documentElement) {
    document.documentElement.classList.add("mdexplore-pdf-export-mode");
  }
  document.body.classList.add("mdexplore-pdf-export-mode");
  for (const fence of Array.from(document.querySelectorAll(".mdexplore-fence"))) {
    if (!(fence instanceof HTMLElement)) {
      continue;
    }
    const sectionWidth = String(fence.style.getPropertyValue("--mdexplore-print-section-width") || "").trim();
    if (sectionWidth) {
      fence.dataset.mdexplorePdfSectionWidth = sectionWidth;
      fence.style.setProperty("width", sectionWidth, "important");
      fence.style.setProperty("max-width", sectionWidth, "important");
      fence.style.setProperty("overflow", "visible", "important");
      for (const child of Array.from(fence.children)) {
        if (!(child instanceof HTMLElement)) {
          continue;
        }
        const tag = String(child.tagName || "").toLowerCase();
        if (!/^h[1-6]$/.test(tag)) {
          continue;
        }
        child.dataset.mdexplorePdfHeadingWidth = sectionWidth;
        child.style.setProperty("display", "block", "important");
        child.style.setProperty("width", sectionWidth, "important");
        child.style.setProperty("max-width", sectionWidth, "important");
        child.style.setProperty("box-sizing", "border-box", "important");
        child.style.setProperty("white-space", "normal", "important");
      }
    }
  }
  for (const shell of Array.from(document.querySelectorAll(".mdexplore-mermaid-shell"))) {
    if (!(shell instanceof HTMLElement)) {
      continue;
    }
    const host = shell.parentElement;
    if (!(host instanceof HTMLElement)) {
      continue;
    }
    host.style.setProperty("display", "block", "important");
    host.style.setProperty("width", "100%", "important");
    host.style.setProperty("max-width", "100%", "important");
    const viewport = shell.querySelector(".mdexplore-mermaid-viewport");
    const svg = viewport instanceof HTMLElement ? viewport.querySelector("svg") : shell.querySelector("svg");
    const plantImg =
      viewport instanceof HTMLElement ? viewport.querySelector("img.plantuml") : shell.querySelector("img.plantuml");
    const plantSvg =
      viewport instanceof HTMLElement
        ? viewport.querySelector("svg.mdexplore-plantuml-inline")
        : shell.querySelector("svg.mdexplore-plantuml-inline");
    if (svg instanceof SVGElement) {
      svg.style.removeProperty("transform");
      svg.removeAttribute("width");
      svg.removeAttribute("height");
      svg.style.removeProperty("width");
      svg.style.setProperty("width", "var(--mdexplore-print-diagram-width, auto)", "important");
      svg.style.setProperty("max-width", "var(--mdexplore-print-diagram-max-width, 100%)", "important");
      svg.style.setProperty("height", "var(--mdexplore-print-diagram-height, auto)", "important");
      svg.style.setProperty("max-height", "var(--mdexplore-print-diagram-max-height, none)", "important");
      host.innerHTML = "";
      host.appendChild(svg);
      continue;
    }
    const normalizedPlant =
      plantSvg instanceof SVGElement ? plantSvg : replacePlantUmlImageWithInlineSvgForPdf(plantImg);
    if (normalizedPlant instanceof SVGElement) {
      normalizePlantUmlInlineSvgForPdf(normalizedPlant);
      host.innerHTML = "";
      host.appendChild(normalizedPlant);
    }
  }
  for (const toolbar of Array.from(document.querySelectorAll(".mdexplore-mermaid-toolbar"))) {
    if (!(toolbar instanceof HTMLElement)) {
      continue;
    }
    toolbar.dataset.mdexplorePdfHidden = "1";
    toolbar.style.setProperty("display", "none", "important");
  }
  for (const viewport of Array.from(document.querySelectorAll(".mdexplore-mermaid-viewport"))) {
    if (!(viewport instanceof HTMLElement)) {
      continue;
    }
    viewport.dataset.mdexplorePdfViewportHidden = "1";
    viewport.scrollLeft = 0;
    viewport.scrollTop = 0;
    viewport.style.setProperty("overflow", "hidden", "important");
    viewport.style.setProperty("scrollbar-width", "none", "important");
    viewport.style.setProperty("-ms-overflow-style", "none", "important");
  }
  for (const img of Array.from(document.querySelectorAll("img.plantuml"))) {
    if (!(img instanceof HTMLImageElement)) {
      continue;
    }
    replacePlantUmlImageWithInlineSvgForPdf(img);
  }
  for (const svg of Array.from(document.querySelectorAll("svg.mdexplore-plantuml-inline"))) {
    normalizePlantUmlInlineSvgForPdf(svg);
  }
  for (const svg of Array.from(document.querySelectorAll(".mermaid svg"))) {
    if (!(svg instanceof SVGElement)) {
      continue;
    }
    svg.style.removeProperty("transform");
    svg.removeAttribute("width");
    svg.removeAttribute("height");
    svg.style.removeProperty("width");
    svg.style.removeProperty("max-width");
    svg.style.removeProperty("height");
    svg.style.setProperty("display", "block", "important");
    svg.style.setProperty("width", "var(--mdexplore-print-diagram-width, auto)", "important");
    svg.style.setProperty("max-width", "var(--mdexplore-print-diagram-max-width, 100%)", "important");
    svg.style.setProperty("height", "var(--mdexplore-print-diagram-height, auto)", "important");
    svg.style.setProperty("max-height", "var(--mdexplore-print-diagram-max-height, none)", "important");
  }
  return true;
})();
"""

        def _print_after_dom_normalized(_result) -> None:
            try:
                # Give layout a brief turn after wrapper flattening before snapshot.
                QTimer.singleShot(
                    70,
                    lambda: self.preview.page().printToPdf(
                        lambda pdf_data, target=output_path, key=source_key: self._on_pdf_render_ready(
                            target, key, pdf_data
                        ),
                    ),
                )
            except Exception as exc:
                self._set_pdf_export_busy(False)
                self._restore_preview_mermaid_palette(source_key)
                error_text = self._truncate_error_text(str(exc), 500)
                QMessageBox.critical(self, "PDF export failed", f"Could not start PDF rendering:\n{error_text}")
                self.statusBar().showMessage(f"PDF export failed: {error_text}", 5000)

        self.preview.page().runJavaScript(preprint_js, _print_after_dom_normalized)

    def _restore_preview_mermaid_palette(self, source_key: str | None = None) -> None:
        """Switch Mermaid back to preview palette after PDF export attempts."""
        js = """
(() => {
  if (document.documentElement) {
    document.documentElement.classList.remove("mdexplore-pdf-export-mode");
  }
  document.body.classList.remove("mdexplore-pdf-export-mode");
  for (const token of Array.from(document.querySelectorAll(".mdexplore-pdf-landscape-token"))) {
    if (token instanceof HTMLElement) {
      token.remove();
    }
  }
  const pdfMermaidOverride = document.getElementById("__mdexplore_pdf_mermaid_light_override");
  if (pdfMermaidOverride && pdfMermaidOverride.parentNode) {
    pdfMermaidOverride.parentNode.removeChild(pdfMermaidOverride);
  }
  for (const toolbar of Array.from(document.querySelectorAll(".mdexplore-mermaid-toolbar[data-mdexplore-pdf-hidden='1']"))) {
    if (!(toolbar instanceof HTMLElement)) {
      continue;
    }
    toolbar.style.removeProperty("display");
    delete toolbar.dataset.mdexplorePdfHidden;
  }
  for (const viewport of Array.from(document.querySelectorAll(".mdexplore-mermaid-viewport[data-mdexplore-pdf-viewport-hidden='1']"))) {
    if (!(viewport instanceof HTMLElement)) {
      continue;
    }
    viewport.style.removeProperty("overflow");
    viewport.style.removeProperty("scrollbar-width");
    viewport.style.removeProperty("-ms-overflow-style");
    delete viewport.dataset.mdexplorePdfViewportHidden;
  }
  for (const svg of Array.from(document.querySelectorAll("svg.mdexplore-plantuml-inline[data-mdexplore-original-img]"))) {
    if (!(svg instanceof SVGElement)) {
      continue;
    }
    const original = String(svg.getAttribute("data-mdexplore-original-img") || "");
    if (!original) {
      continue;
    }
    try {
      const container = document.createElement("div");
      container.innerHTML = original;
      const replacement = container.firstElementChild;
      if (replacement instanceof HTMLImageElement) {
        svg.replaceWith(replacement);
      }
    } catch (_error) {
      // Ignore restore failures; a later preview rerender will recover.
    }
  }
  for (const fence of Array.from(document.querySelectorAll(".mdexplore-fence"))) {
    if (!(fence instanceof HTMLElement)) {
      continue;
    }
    fence.style.removeProperty("min-height");
    fence.style.removeProperty("width");
    fence.style.removeProperty("max-width");
    fence.style.removeProperty("overflow");
    delete fence.dataset.mdexplorePdfSectionWidth;
    for (const child of Array.from(fence.children)) {
      if (!(child instanceof HTMLElement)) {
        continue;
      }
      delete child.dataset.mdexplorePdfHeadingWidth;
      child.style.removeProperty("width");
      child.style.removeProperty("max-width");
      child.style.removeProperty("box-sizing");
      child.style.removeProperty("white-space");
    }
  }
  for (const block of Array.from(document.querySelectorAll(".mdexplore-print-block[data-mdexplore-print-block='1']"))) {
    if (!(block instanceof HTMLElement)) {
      continue;
    }
    const parent = block.parentNode;
    if (!parent) {
      continue;
    }
    while (block.firstChild) {
      parent.insertBefore(block.firstChild, block);
    }
    parent.removeChild(block);
  }
  const reapplyAll = () => {
    for (const shell of Array.from(document.querySelectorAll(".mdexplore-mermaid-shell"))) {
      const fn = shell && shell.__mdexploreReapplySavedState;
      if (typeof fn !== "function") {
        continue;
      }
      try {
        fn();
      } catch (_error) {
        // Ignore per-shell restore failures.
      }
    }
  };
  if (window.__mdexploreRunClientRenderers) {
    const maybePromise = window.__mdexploreRunClientRenderers({ mermaidMode: "auto", forceMermaid: true });
    Promise.resolve(maybePromise).then(() => reapplyAll()).catch(() => reapplyAll());
    return true;
  }
  if (window.__mdexploreRunMermaidWithMode) {
    const maybePromise = window.__mdexploreRunMermaidWithMode("auto", false);
    Promise.resolve(maybePromise).then(() => reapplyAll()).catch(() => reapplyAll());
    return true;
  }
  reapplyAll();
  return false;
})();
"""
        self.preview.page().runJavaScript(js)
        if source_key:
            self._reapply_diagram_view_state_for(source_key)
            QTimer.singleShot(120, lambda key=source_key: self._reapply_diagram_view_state_for(key))
            QTimer.singleShot(420, lambda key=source_key: self._reapply_diagram_view_state_for(key))
            QTimer.singleShot(980, lambda key=source_key: self._reapply_diagram_view_state_for(key))

    def _on_pdf_render_ready(self, output_path: Path, source_key: str, pdf_data) -> None:
        """Receive raw PDF bytes from WebEngine and start footer stamping."""
        try:
            raw_pdf = bytes(pdf_data)
        except Exception:
            raw_pdf = b""

        if not raw_pdf:
            self._set_pdf_export_busy(False)
            self._restore_preview_mermaid_palette(source_key)
            message = "Qt WebEngine returned an empty PDF payload"
            QMessageBox.critical(self, "PDF export failed", message)
            self.statusBar().showMessage(f"PDF export failed: {message}", 5000)
            return

        layout_hints = dict(self._pending_pdf_layout_hints)
        self._pending_pdf_layout_hints = {}
        worker = PdfExportWorker(output_path, raw_pdf, layout_hints)
        self._active_pdf_workers.add(worker)
        worker.signals.finished.connect(
            lambda path_text, error_text, current_worker=worker, key=source_key: self._on_pdf_export_finished(
                current_worker,
                path_text,
                error_text,
                key,
            )
        )
        self._pdf_pool.start(worker)
        self.statusBar().showMessage(f"Writing numbered PDF: {output_path.name}...")

    def _on_pdf_export_finished(
        self, worker: PdfExportWorker, output_path_text: str, error_text: str, source_key: str
    ) -> None:
        """Finalize async PDF export and report result."""
        self._active_pdf_workers.discard(worker)
        self._set_pdf_export_busy(False)
        self._restore_preview_mermaid_palette(source_key)
        self._pdf_export_source_key = None

        if error_text:
            short_error = self._truncate_error_text(error_text, 500)
            QMessageBox.critical(
                self,
                "PDF export failed",
                f"Could not create PDF:\n{output_path_text}\n\n{short_error}",
            )
            self.statusBar().showMessage(f"PDF export failed: {short_error}", 5000)
            return

        self.statusBar().showMessage(f"Exported PDF: {output_path_text}", 5000)

    def _edit_current_file(self) -> None:
        """Open the selected markdown file in VS Code."""
        if self.current_file is None:
            QMessageBox.information(self, "No file selected", "Select a markdown file before using Edit.")
            return
        try:
            subprocess.Popen(["code", str(self.current_file)])
        except FileNotFoundError:
            QMessageBox.critical(
                self,
                "VS Code not found",
                "Could not find 'code' in PATH. Install VS Code or add the 'code' launcher command.",
            )


def main() -> int:
    parser = argparse.ArgumentParser(
        prog="mdexplore",
        description="Browse and preview markdown files with rich rendering.",
    )
    parser.add_argument(
        "path",
        nargs="?",
        default=None,
        help="Root directory to browse (default: ~/.mdexplore.cfg path, or home directory).",
    )
    parser.add_argument(
        "--mermaid-backend",
        choices=[MERMAID_BACKEND_JS, MERMAID_BACKEND_RUST],
        default=MERMAID_BACKEND_JS,
        help="Mermaid render backend: 'js' (default) or 'rust' (requires mmdr).",
    )
    args = parser.parse_args()

    root = Path(args.path).expanduser() if args.path is not None else _load_default_root_from_config()
    if not root.exists():
        print(f"Path does not exist: {root}", file=sys.stderr)
        return 2
    if not root.is_dir():
        print(f"Path is not a directory: {root}", file=sys.stderr)
        return 2

    # Prefer GPU by default; only force software rendering if no OpenGL context
    # can be created before QApplication initialization.
    gpu_context_available = _gpu_context_available()
    if not gpu_context_available:
        _configure_qt_graphics_fallback()

    app = QApplication(sys.argv)
    app.setApplicationName("mdexplore")
    # Explicit desktop file name improves Linux shell mapping between the
    # running window and mdexplore.desktop for icon/pinning behavior.
    app.setDesktopFileName("mdexplore")
    app_icon = _build_markdown_icon()
    app.setWindowIcon(app_icon)
    window = MdExploreWindow(
        root,
        app_icon,
        _config_file_path(),
        mermaid_backend=str(args.mermaid_backend or MERMAID_BACKEND_JS),
        gpu_context_available=gpu_context_available,
    )
    window.show()
    return app.exec()


if __name__ == "__main__":
    raise SystemExit(main())
