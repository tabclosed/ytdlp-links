"""
    QMainWindow
    └── central (QWidget)
        ├── main_splitter (QSplitter, vertical)
        │   ├── upper_splitter (QSplitter, horizontal)
        │   │   ├── left_column (QWidget)
        │   │   │   ├── url_widget (QWidget)
        │   │   │   │   └── url_line_edit (QLineEdit)
        │   │   │   └── left_widget (QWidget)
        │   │   │       └── left_stack (QStackedWidget)
        │   │   │           ├── url_list_page (QWidget)      — index 0
        │   │   │           │   └── url_list (QTreeWidget)   — urls + folders
        │   │   │           └── settings_page (QWidget)      — index 1
        │   │   │               ├── tab bar (centered): General / Connection / Profiles / Scheduler / Plugins / About
        │   │   │               └── settings_stack (QStackedWidget, full width)
        │   │   │                   ├── settings_general      — index 0
        │   │   │                   ├── settings_connection   — index 1
        │   │   │                   ├── settings_profiles     — index 2
        │   │   │                   ├── settings_scheduler    — index 3
        │   │   │                   ├── settings_plugins      — index 4
        │   │   │                   └── settings_about        — index 5
        │   │   └── right_stack (QStackedWidget)
        │   │       ├── sidebar_scroll (QScrollArea)         — index 0
        │   │       │   └── sidebar_panel (QWidget)
        │   │       └── settings_sidebar_content (QWidget)      — index 1
        │   │           └── shared title/note label, updated per settings tab
        │   └── log_container (QWidget)
        │       └── log (QTextEdit)
        └── button_row
"""
import json
import math
import os
import platform
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
import zipfile
from pathlib import Path

from PySide6.QtCore import (
    QEvent, QObject, QPoint, QPointF, QRegularExpression, QRunnable, QSize, Qt,
    QThreadPool, QTime, QTimer, QUrl, Signal,
)
from PySide6.QtNetwork import QLocalServer, QLocalSocket
from PySide6.QtGui import (
    QColor, QDesktopServices, QFontMetrics, QGuiApplication, QIcon, QPainter, QPalette,
    QPen, QPixmap, QPolygonF, QRegularExpressionValidator, QTextCursor,
)
from PySide6.QtWidgets import (
    QAbstractItemView, QApplication, QButtonGroup, QCheckBox, QComboBox,
    QDialog, QDialogButtonBox, QFileDialog, QFormLayout, QFrame, QHBoxLayout,
    QInputDialog, QLabel, QLineEdit,
    QListWidget, QListWidgetItem, QMainWindow, QMenu, QMessageBox, QPushButton,
    QRadioButton,
    QScrollArea, QScrollBar, QSizePolicy, QSpinBox, QSplitter, QStackedWidget, QStyle,
    QStyledItemDelegate, QStyleOptionViewItem, QTextBrowser, QTextEdit, QTimeEdit,
    QTreeWidget, QTreeWidgetItem, QVBoxLayout, QWidget,
)

# The app's (only) color palette. Keys become module globals via set_theme_colors().
THEMES = {
    "dark": {
        "BG_PANEL": "#2b2b2b",
        "BG_BUTTON": "#3c3c3c",
        "BG_BUTTON_HOVER": "#4c4c4c",
        "BG_SEARCH_HIGHLIGHT": "#4c4c4c",
        "BG_THUMBNAIL": "#1f1f1f",
        "BG_WINDOW": "#232323",
        "BG_LOG": "#2b2b2b",
        "BORDER": "#555555",
        "BORDER_DISABLED": "#444444",
        "BORDER_THUMBNAIL": "#111111",
        "BORDER_FOCUS": "#2bb3a3",
        "TEXT_PRIMARY": "#ffffff",
        "TEXT_SECONDARY": "#cccccc",
        "TEXT_MUTED": "#999999",
        "TEXT_FAINT": "#666666",
    },
}


# Rebind the module-level color globals to the given theme's palette
def set_theme_colors(name):
    globals().update(THEMES[name])


# Load the (only) theme's colors
set_theme_colors("dark")


# Path to the cached dropdown-arrow icon used by combo boxes
def _combo_down_arrow_path():
    # Renders (once per color, then cached on disk) a small solid downward
    # triangle PNG for use in QComboBox::down-arrow's image: url(...). Qt's
    # QSS url() only resolves real file paths - not data: URIs - and a
    # border-color CSS triangle trick renders as a filled box rather than a
    # triangle for this particular subcontrol, so an actual file it is.
    return _triangle_icon_path("combo_arrow", TEXT_SECONDARY, "down")


_SCROLLBAR_SIZE = 12  # width/height of the scrollbar track and its arrow buttons
_SCROLLBAR_GAP = 2  # the thin transparent margin left on one side (see scrollbar_style)


def _scrollbar_arrow_path(direction, state="rest"):
    # Same rationale/technique as _combo_down_arrow_path above: QScrollBar's
    # ::up-arrow/::down-arrow/::left-arrow/::right-arrow subcontrols also
    # render a plain filled box instead of a triangle with the CSS
    # border-trick, so these are real cached PNG files referenced via
    # image: url(...) too. Three states stand in for the :hover/:pressed
    # pseudo-classes, since url() itself can't be conditioned on them:
    # "rest" is fully transparent (arrow hidden until interacted with),
    # "hover" is the normal dim color, "pressed" is the brighter color
    # for click feedback.
    #
    # Qt always gives these subcontrols the scrollbar's full margin-box
    # size, not just the narrowed `width`/`height` from the QSS rule - for
    # up/down that's `_SCROLLBAR_SIZE + _SCROLLBAR_GAP` wide (the gap is on
    # the right), for left/right it's that much taller (the gap is on the
    # bottom). Handing it a plain square PNG means Qt stretches it to fill
    # that wider/taller box, visibly skewing the glyph sideways - so the
    # icon canvas below matches the real box exactly, with the glyph flush
    # in the handle-sized corner and the extra gap left blank, rather than
    # fighting the stretch with a guessed pixel offset.
    canvas = (
        (_SCROLLBAR_SIZE + _SCROLLBAR_GAP, _SCROLLBAR_SIZE)
        if direction in ("up", "down")
        else (_SCROLLBAR_SIZE, _SCROLLBAR_SIZE + _SCROLLBAR_GAP)
    )
    if state == "rest":
        return _blank_icon_path(canvas)
    color = TEXT_PRIMARY if state == "pressed" else TEXT_SECONDARY
    name = f"scrollbar_arrow_{direction}_{state}"
    return _triangle_icon_path(
        name, color, direction, glyph_size=_SCROLLBAR_SIZE, canvas_size=canvas, bg_color=BG_BUTTON_HOVER
    )


# Directory the app is running from (handles both frozen and script execution)
def _app_dir():
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


# This app's own private scratch space for anything that would otherwise land in
# the shared, system-wide temp directory (tempfile.gettempdir(), e.g. C:\Users\
# <user>\AppData\Local\Temp or /tmp) - kept next to the executable/script instead so
# the whole app stays portable and self-contained: move or delete the exe's folder
# (or the whole USB stick/portable drive it's running from) and nothing is left
# behind anywhere else on the system, and nothing here is visible to or shared with
# any other app or user account. Created on first use; safe to call repeatedly.
def _app_temp_dir():
    path = _app_dir() / "temp"
    try:
        path.mkdir(parents=True, exist_ok=True)
    except OSError:
        pass
    return path


def _blank_icon_path(size=9):
    # Fully transparent canvas, cached once per size and shared by every
    # direction - used as the scrollbar arrows' resting-state image so
    # they're invisible until hovered or pressed. `size` may be an int
    # (square) or (width, height) tuple, matching the real subcontrol box
    # so Qt has nothing to stretch even though it's blank either way.
    w, h = (size, size) if isinstance(size, int) else size
    cache_dir = _app_temp_dir() / "ui_template_icons_v2"
    cache_dir.mkdir(parents=True, exist_ok=True)
    icon_path = cache_dir / f"blank_{w}x{h}.png"
    if not icon_path.exists():
        pixmap = QPixmap(w, h)
        pixmap.fill(Qt.GlobalColor.transparent)
        pixmap.save(str(icon_path), "PNG")
    return icon_path.as_posix()


# Render (and cache on disk) a small solid triangle PNG for use as a QSS icon
def _triangle_icon_path(cache_name, color, direction, glyph_size=9, canvas_size=None, bg_color=None):
    # `glyph_size` is the (square) size the triangle itself - and its
    # `bg_color` hover/pressed highlight, if given - is drawn at, flush in
    # the canvas's top-left corner. `canvas_size` is the size of the PNG
    # itself; when it's larger than `glyph_size` (see _scrollbar_arrow_path)
    # the extra strip is simply left transparent, so Qt has an exact-size
    # image to place rather than one it has to stretch. Defaults to a plain
    # glyph_size x glyph_size square for callers (like the combo box
    # down-arrow) that don't need the extra canvas room.
    canvas_w, canvas_h = canvas_size or (glyph_size, glyph_size)
    cache_dir = _app_temp_dir() / "ui_template_icons_v2"
    cache_dir.mkdir(parents=True, exist_ok=True)
    bg_suffix = f"_bg{bg_color.lstrip('#')}" if bg_color else ""
    icon_path = (
        cache_dir
        / f"{cache_name}_{glyph_size}_{canvas_w}x{canvas_h}_{color.lstrip('#')}{bg_suffix}.png"
    )
    if not icon_path.exists():
        pixmap = QPixmap(canvas_w, canvas_h)
        pixmap.fill(Qt.GlobalColor.transparent)
        painter = QPainter(pixmap)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        scale = glyph_size / 9
        radius = 4 * scale
        if bg_color:
            painter.setBrush(QColor(bg_color))
            painter.setPen(Qt.PenStyle.NoPen)
            painter.drawRoundedRect(0, 0, glyph_size, glyph_size, radius, radius)
        painter.setBrush(QColor(color))
        painter.setPen(Qt.PenStyle.NoPen)
        points = {
            "down": [QPoint(2, 3), QPoint(7, 3), QPoint(5, 7)],
            "up": [QPoint(2, 6), QPoint(7, 6), QPoint(5, 2)],
            "left": [QPoint(6, 2), QPoint(6, 7), QPoint(2, 5)],
            "right": [QPoint(3, 2), QPoint(3, 7), QPoint(7, 5)],
        }[direction]
        points = [QPointF(p.x() * scale, p.y() * scale) for p in points]
        painter.drawPolygon(QPolygonF(points))
        painter.end()
        pixmap.save(str(icon_path), "PNG")
    return icon_path.as_posix()


# Cache dir shared by every rendered-icon helper in this module (gear, arrows, etc.)
# Bump this whenever a glyph's drawing code changes below - it's baked into the
# cache filename so edits actually take effect instead of loading a stale PNG
# left over from a previous run.
_ICON_ASSET_VERSION = 4

_ICON_CACHE_DIR = _app_temp_dir() / "ui_template_icons_v2"


# Render (and cache on disk) a small flat glyph icon in the given color, for use
# as a QPushButton's setIcon(). `kind` selects the glyph; size is the square
# canvas in px. Used by the bottom action row (Settings/Probe/Download/
# Refresh/Minimize Log/Exit) so each button gets both a colored icon and label.
def _flat_icon_path(kind, color, size=16):
    _ICON_CACHE_DIR.mkdir(parents=True, exist_ok=True)
    icon_path = _ICON_CACHE_DIR / f"flat_{kind}_{size}_v{_ICON_ASSET_VERSION}_{color.lstrip('#')}.png"
    if icon_path.exists():
        return icon_path.as_posix()

    pixmap = QPixmap(size, size)
    pixmap.fill(Qt.GlobalColor.transparent)
    painter = QPainter(pixmap)
    painter.setRenderHint(QPainter.RenderHint.Antialiasing)
    pen = QPen(QColor(color))
    pen.setWidthF(size / 10)
    pen.setCapStyle(Qt.PenCapStyle.RoundCap)
    pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
    painter.setPen(pen)
    painter.setBrush(Qt.BrushStyle.NoBrush)

    m = size * 0.18  # inner margin so strokes don't clip at the edges
    inner = size - 2 * m

    if kind == "settings":
        # Circle with 6 short radial teeth, gear-ish at a glance
        r = inner * 0.32
        cx = cy = size / 2
        painter.drawEllipse(QPointF(cx, cy), r, r)
        for i in range(6):
            angle = i * 60
            rad = math.radians(angle)
            x1, y1 = cx + math.cos(rad) * r * 1.35, cy + math.sin(rad) * r * 1.35
            x2, y2 = cx + math.cos(rad) * r * 1.9, cy + math.sin(rad) * r * 1.9
            painter.drawLine(QPointF(x1, y1), QPointF(x2, y2))

    elif kind == "eye":
        cx = size / 2
        cy = size / 2 + 2
        half_w = inner * 0.52
        half_h = inner * 0.32
        painter.drawArc(
            int(cx - half_w), int(cy - half_h), int(half_w * 2), int(half_h * 2),
            0, 180 * 16,
        )
        painter.drawArc(
            int(cx - half_w), int(cy - half_h), int(half_w * 2), int(half_h * 2),
            180 * 16, 180 * 16,
        )
        painter.setBrush(QColor(color))
        pupil_r = inner * 0.15
        painter.drawEllipse(QPointF(cx, cy), pupil_r, pupil_r)

    elif kind == "download":
        cx = size / 2
        top, bottom = m, m + inner * 0.62
        painter.drawLine(QPointF(cx, top), QPointF(cx, bottom))
        arrow = inner * 0.22
        painter.drawLine(QPointF(cx - arrow, bottom - arrow), QPointF(cx, bottom))
        painter.drawLine(QPointF(cx + arrow, bottom - arrow), QPointF(cx, bottom))
        tray_y = m + inner
        painter.drawLine(QPointF(m, tray_y), QPointF(m + inner, tray_y))

    elif kind == "refresh":
        rect_size = inner * 0.95
        rect_x = size / 2 - rect_size / 2
        rect_y = size / 2 - rect_size / 2 + 1
        painter.drawArc(int(rect_x), int(rect_y), int(rect_size), int(rect_size), 20 * 16, 300 * 16)
        end_angle = math.radians(20)
        ex = size / 2 + (rect_size / 2) * math.cos(end_angle)
        ey = size / 2 - (rect_size / 2) * math.sin(end_angle) + 1
        painter.setBrush(QColor(color))
        head = size * 0.14
        arrow_pts = [
            QPointF(ex - head, ey - head * 0.3),
            QPointF(ex + head * 0.2, ey - head),
            QPointF(ex + head * 0.4, ey + head * 0.4),
        ]
        painter.drawPolygon(QPolygonF(arrow_pts))

    elif kind == "minimize":
        y = size / 2
        painter.drawLine(QPointF(m, y), QPointF(m + inner, y))

    painter.end()
    pixmap.save(str(icon_path), "PNG")
    return icon_path.as_posix()


# Shared padding/corner-radius fragment reused by button_style()
_BUTTON_BASE = "padding: 5px; border-radius: 3px;"

# Shared panel skin (background, no border, rounded corners) for top-level content panels
_PANEL_BASE = "background-color: {bg}; border: none; border-radius: 5px;"


# Shared background/border style for top-level content panels
def panel_style():
    return _PANEL_BASE.format(bg=BG_PANEL)


# Small secondary-colored text style for sidebar and form labels
def sidebar_label_muted_style():
    return f"color: {TEXT_SECONDARY}; font-size: 11px;"


# Highlight style applied to a settings row that matches the live search
def settings_search_highlight_style():
    return (
        f"background-color: {BG_SEARCH_HIGHLIGHT}; color: {TEXT_PRIMARY}; "
        f"border-radius: 4px; padding: 2px 6px;"
    )


# Thin horizontal rule style used to divide sidebar sections
def separator_style(margin_top=10, margin_bottom=0):
    style = f"color: {BORDER_DISABLED}; margin-top: {margin_top}px;"
    if margin_bottom:
        style += f" margin-bottom: {margin_bottom}px;"
    return style


# Style for right-click context menus
def menu_style():
    return (
        f"QMenu {{ background-color: {BG_BUTTON}; color: {TEXT_PRIMARY}; "
        f"border: 1px solid {BORDER}; padding: 4px; }} "
        f"QMenu::item {{ padding: 5px 20px; border-radius: 3px; }} "
        f"QMenu::item:selected {{ background-color: {BG_BUTTON_HOVER}; "
        f"color: {TEXT_PRIMARY}; }} "
        f"QMenu::separator {{ height: 1px; background: {BORDER}; margin: 4px 0px; }}"
    )


# Button used in the bottom action row: full-width rounded hover background
# (plain QSS) plus a custom-painted underline that's narrower than the button
# itself (UNDERLINE_INSET px removed from each side) - QSS can't do this
# because a border always spans the same box as the background, so the line
# has to be drawn by hand in paintEvent instead of via border-bottom.
class UnderlineButton(QPushButton):
    UNDERLINE_WIDTH_RATIO = 0.95  # underline length as a fraction of the button's own width
    UNDERLINE_THICKNESS = 2

    def __init__(self, text, text_color, underline_color, parent=None):
        super().__init__(text, parent)
        self.setAttribute(Qt.WidgetAttribute.WA_Hover, True)
        self._text_color = text_color
        self._underline_color = underline_color
        self._active = False
        self.setStyleSheet(
            f"QPushButton {{ background-color: transparent; color: {self._text_color}; "
            f"border: none; padding: 5px 10px; border-radius: 3px; }} "
            f"QPushButton:hover {{ background-color: {BG_BUTTON_HOVER}; }} "
            f"QPushButton:disabled {{ color: {TEXT_FAINT}; background-color: transparent; }}"
        )

    # Force the underline to stay in its hover color permanently (used for the
    # Settings button while its panel is open)
    def set_active(self, active):
        if self._active != active:
            self._active = active
            self.update()

    def paintEvent(self, event):
        super().paintEvent(event)
        if self.isCheckable():
            # Tab-button mode: no underline at all unless selected - no gray
            # default line, and hovering an unselected tab doesn't draw one either
            if not (self.isEnabled() and self.isChecked()):
                return
            color = self._underline_color
        else:
            color = (
                self._underline_color if self.isEnabled() and (self._active or self.underMouse())
                else BORDER_DISABLED
            )
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        pen = QPen(QColor(color))
        pen.setWidthF(self.UNDERLINE_THICKNESS)
        pen.setCapStyle(Qt.PenCapStyle.RoundCap)
        painter.setPen(pen)
        y = self.height() - self.UNDERLINE_THICKNESS / 2 - 1
        inset = self.width() * (1 - self.UNDERLINE_WIDTH_RATIO) / 2
        painter.drawLine(
            QPointF(inset, y),
            QPointF(self.width() - inset, y),
        )
        painter.end()

    def enterEvent(self, event):
        super().enterEvent(event)
        self.update()

    def leaveEvent(self, event):
        super().leaveEvent(event)
        self.update()





# Standard push-button style used throughout the app
def button_style():
    return (
        f"QPushButton {{ background-color: {BG_BUTTON}; color: {TEXT_SECONDARY}; "
        f"border: 1px solid {BORDER}; {_BUTTON_BASE} }} "
        f"QPushButton:hover {{ background-color: {BG_BUTTON_HOVER}; }} "
        f"QPushButton:disabled {{ background-color: {BG_PANEL}; color: {TEXT_FAINT}; "
        f"border: 1px solid {BORDER_DISABLED}; }}"
    )


# Style for line edits, spin boxes, and combo boxes on settings pages
def settings_input_style():
    return (
        f"QLineEdit, QSpinBox, QComboBox {{ background-color: {BG_THUMBNAIL}; "
        f"color: {TEXT_PRIMARY}; border: 1px solid {BORDER}; border-radius: 4px; "
        f"padding: 4px 6px; }} "
        f"QComboBox::drop-down {{ subcontrol-origin: padding; subcontrol-position: top right; "
        f"width: 20px; border: none; background: transparent; }} "
        f"QComboBox::down-arrow {{ image: url({_combo_down_arrow_path()}); "
        f"width: 10px; height: 10px; }} "
        f"QComboBox QAbstractItemView {{ background-color: {BG_THUMBNAIL}; "
        f"color: {TEXT_PRIMARY}; border: 1px solid {BORDER}; outline: none; "
        f"selection-background-color: {BG_BUTTON_HOVER}; selection-color: {TEXT_PRIMARY}; }} "
        f"QComboBox QAbstractItemView::item {{ padding: 4px 6px; min-height: 22px; }}"
    )


# Style for checkboxes
def checkbox_style():
    return (
        f"QCheckBox {{ color: {TEXT_PRIMARY}; font-size: 13px; spacing: 8px; }} "
        f"QCheckBox::indicator {{ width: 14px; height: 14px; border: 1px solid {BORDER}; "
        f"border-radius: 3px; background-color: {BG_THUMBNAIL}; }} "
        f"QCheckBox::indicator:checked {{ background-color: {BORDER_FOCUS}; "
        f"border: 1px solid {BORDER_FOCUS}; }}"
    )


# Style for radio buttons, e.g. the Name/URL mode toggle in the search dialog
def radio_button_style():
    return (
        f"QRadioButton {{ color: {TEXT_PRIMARY}; font-size: 13px; spacing: 8px; }} "
        f"QRadioButton::indicator {{ width: 14px; height: 14px; border: 1px solid {BORDER}; "
        f"border-radius: 7px; background-color: {BG_THUMBNAIL}; }} "
        f"QRadioButton::indicator:checked {{ background-color: {BORDER_FOCUS}; "
        f"border: 1px solid {BORDER_FOCUS}; }}"
    )


# Style for the profile list widget
def profile_list_style():
    return (
        f"QListWidget {{ background-color: {BG_THUMBNAIL}; color: {TEXT_PRIMARY}; "
        f"border: 1px solid {BORDER}; border-radius: 4px; outline: none; }} "
        f"QListWidget::item {{ padding: 3px 6px; }} "
        f"QListWidget::item:hover {{ background-color: {BG_BUTTON}; }} "
        f"QListWidget::item:selected {{ background-color: {BG_BUTTON_HOVER}; color: {TEXT_PRIMARY}; }}"
    )


# Style for the main URL input line edit
def line_edit_style():
    return (
        f"QLineEdit {{ background-color: {BG_THUMBNAIL}; color: {TEXT_PRIMARY}; "
        f"border: none; border-bottom: 2px solid {BORDER}; padding: 5px; "
        f"border-top-left-radius: 5px; border-top-right-radius: 5px; "
        f"border-bottom-left-radius: 0px; border-bottom-right-radius: 0px; }} "
        f"QLineEdit:focus {{ border-bottom: 2px solid {BORDER_FOCUS}; }}"
    )


# Item delegate that suppresses the dotted focus rectangle on tree items
# Item delegate that suppresses the dotted focus rectangle, keeps failed-probe rows
# yellow, completed-download rows green, disabled rows greyed out, skipped rows
# blue, and members-only rows red - all regardless of selection/hover, since the
# QSS state selectors would otherwise repaint them back to normal colors. Folder
# rows get the same green treatment, but only when every link nested anywhere
# inside them is either skipped or fully downloaded - any other status among its
# descendants (failed, members-only, disabled, timed out, or simply not done
# yet) leaves the folder at the normal text color instead.
class _NoFocusRectDelegate(QStyledItemDelegate):
    # All leaf link items nested anywhere under `item` (recursing into subfolders),
    # skipping the synthetic "load more" row - same traversal as
    # MainWindow._iter_all_link_items, duplicated here since the delegate only
    # has the tree widget, not the MainWindow, to work with
    def _folder_link_items(self, item):
        for i in range(item.childCount()):
            child = item.child(i)
            if child.data(0, IS_LOAD_MORE_ROLE):
                continue
            if child.data(0, IS_FOLDER_ROLE):
                yield from self._folder_link_items(child)
            else:
                yield child

    # Suppress the focus dotted-rect and recolor the row's text for members-only,
    # disabled, or skipped links (or, for a folder row, green once everything
    # nested inside it is skipped/downloaded)
    def paint(self, painter, option, index):
        opt = QStyleOptionViewItem(option)
        opt.state &= ~QStyle.StateFlag.State_HasFocus
        if index.data(IS_FOLDER_ROLE):
            tree = self.parent()
            item = tree.itemFromIndex(index) if tree is not None else None
            links = list(self._folder_link_items(item)) if item is not None else []
            if links and all(
                l.data(0, LINK_SKIPPED_ROLE) or l.data(0, DOWNLOAD_PROGRESS_ROLE) == 100
                for l in links
            ):
                color = QColor(DOWNLOAD_COMPLETE_COLOR)
                opt.palette.setColor(QPalette.ColorRole.Text, color)
                opt.palette.setColor(QPalette.ColorRole.HighlightedText, color)
            super().paint(painter, opt, index)
            return
        if index.data(MEMBERS_ONLY_ROLE):
            color = QColor(MEMBERS_ONLY_COLOR)
            opt.palette.setColor(QPalette.ColorRole.Text, color)
            opt.palette.setColor(QPalette.ColorRole.HighlightedText, color)
        elif index.data(LINK_DISABLED_ROLE):
            color = QColor(TEXT_FAINT)
            opt.palette.setColor(QPalette.ColorRole.Text, color)
            opt.palette.setColor(QPalette.ColorRole.HighlightedText, color)
        elif index.data(LINK_SKIPPED_ROLE):
            color = QColor(SKIPPED_COLOR)
            opt.palette.setColor(QPalette.ColorRole.Text, color)
            opt.palette.setColor(QPalette.ColorRole.HighlightedText, color)
        elif index.data(PROBE_FAILED_ROLE):
            color = QColor(PROBE_FAILED_COLOR)
            opt.palette.setColor(QPalette.ColorRole.Text, color)
            opt.palette.setColor(QPalette.ColorRole.HighlightedText, color)
        elif index.data(DOWNLOAD_TIMEOUT_ROLE):
            color = QColor(DOWNLOAD_TIMEOUT_COLOR)
            opt.palette.setColor(QPalette.ColorRole.Text, color)
            opt.palette.setColor(QPalette.ColorRole.HighlightedText, color)
        elif index.data(DOWNLOAD_PROGRESS_ROLE) == 100:
            color = QColor(DOWNLOAD_COMPLETE_COLOR)
            opt.palette.setColor(QPalette.ColorRole.Text, color)
            opt.palette.setColor(QPalette.ColorRole.HighlightedText, color)
        super().paint(painter, opt, index)


# Item delegate for the profile list that paints a full-width horizontal divider,
# vertically centered in its row, for any item flagged with
# PROFILE_LIST_SEPARATOR_ROLE (see _add_profile_list_separator). Painting it
# directly here rather than via setItemWidget sidesteps Qt's quirky handling of a
# fixed-height widget's geometry inside setItemWidget (which was clamping/
# mispositioning the line instead of centering it), and guarantees the line is
# both genuinely full-width and evenly padded above and below every time.
class _ProfileListSeparatorDelegate(QStyledItemDelegate):
    # Draw a thin separator line instead of a normal row for items flagged as
    # profile-list separators
    def paint(self, painter, option, index):
        if not index.data(PROFILE_LIST_SEPARATOR_ROLE):
            super().paint(painter, option, index)
            return
        painter.save()
        painter.fillRect(option.rect, QColor(BG_THUMBNAIL))
        y = option.rect.center().y()
        painter.setPen(QColor(BORDER_DISABLED))
        painter.drawLine(option.rect.left(), y, option.rect.right(), y)
        painter.restore()


# Style for the URL/folder tree widget
def url_list_style():
    return (
        f"QTreeWidget {{ background: transparent; color: {TEXT_PRIMARY}; "
        f"border: none; font-size: 13px; outline: none; }} "
        f"QTreeWidget::item {{ padding: 5px 4px; border-radius: 0px; }} "
        f"QTreeWidget::item:hover {{ background-color: {BG_BUTTON}; border-radius: 0px; }} "
        f"QTreeWidget::item:selected {{ background-color: {BG_BUTTON_HOVER}; "
        f"border-radius: 0px; }} "
        f"QTreeWidget::item:selected:hover {{ background-color: {BG_BUTTON_HOVER}; "
        f"border-radius: 0px; }} "
        f"QTreeWidget::item:selected:!active {{ background-color: {BG_BUTTON_HOVER}; "
        f"border-radius: 0px; }}"
    )


# Style for the log text area
def log_style():
    return f"background-color: {BG_LOG}; color: {TEXT_SECONDARY}; border: none; padding: 4px;"


# Style for splitter drag handles
def splitter_handle_style():
    return (
        f"QSplitter::handle {{ background-color: {BG_WINDOW}; }} "
        f"QSplitter::handle:hover {{ background-color: {BORDER}; }}"
    )


class ScrollBarHoverFilter(QObject):
    # QSS can only make a scrollbar arrow glyph react to :hover on that
    # arrow's own tiny rect, which reads as flickery/inconsistent - move the
    # mouse anywhere else on the same scrollbar (track, handle, the *other*
    # arrow) and the glyph you just saw disappears. Users expect entering
    # the scrollbar's column at all to reveal both arrows together and keep
    # them visible until the mouse leaves that column. Installed once,
    # app-wide, on QApplication so it covers every QScrollBar Qt creates for
    # any scroll area without touching each one individually.
    def eventFilter(self, obj, event):
        if isinstance(obj, QScrollBar):
            event_type = event.type()
            if event_type == QEvent.Type.Enter:
                obj.setProperty("hoverArrows", True)
                obj.style().unpolish(obj)
                obj.style().polish(obj)
                obj.update()
            elif event_type == QEvent.Type.Leave:
                obj.setProperty("hoverArrows", False)
                obj.style().unpolish(obj)
                obj.style().polish(obj)
                obj.update()
        return False


# Apply the app-wide scrollbar stylesheet
def apply_scrollbar_style(app):
    # Re-applies the scrollbar QSS (called on init and again after settings
    # changes, since colors are baked into the stylesheet string). The hover
    # filter only needs installing once per app instance - a property on the
    # app itself tracks that, since re-running this must not stack a second
    # filter and double up the enter/leave handling.
    if app is None:
        return
    app.setStyleSheet(scrollbar_style())
    if not app.property("_scrollbarHoverFilterInstalled"):
        app.installEventFilter(ScrollBarHoverFilter(app))
        app.setProperty("_scrollbarHoverFilterInstalled", True)


def scrollbar_style():
    # Thin scrollbar with clickable arrow buttons at each end, applied
    # app-wide via QApplication.setStyleSheet() so it covers every
    # scrollable widget - url tree, log, profile list, combo-box popups,
    # etc. - without having to touch each widget's own stylesheet. The
    # arrow buttons stay background-less and their glyphs invisible at
    # rest, fading in on hover (brighter still while pressed) so they don't
    # clutter the track when the person isn't interacting with it. The
    # glyphs themselves come from small cached PNGs (see
    # _scrollbar_arrow_path) since QSS's border-triangle trick renders as a
    # plain filled box rather than a triangle for these subcontrols - same
    # issue/fix as the combo box's down-arrow above.
    size = _SCROLLBAR_SIZE
    handle_min = 34  # min-height/min-width of the drag handle
    radius = 5
    return (
        f"QScrollBar:vertical {{ background: transparent; width: {size}px; "
        f"margin: {size}px 2px {size}px 0px; }} "
        f"QScrollBar::handle:vertical {{ background: {BORDER}; min-height: {handle_min}px; "
        f"border-radius: {radius}px; }} "
        f"QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {{ "
        f"height: {size}px; background: transparent; border: none; "
        f"border-radius: {radius}px; subcontrol-origin: margin; }} "
        f"QScrollBar::sub-line:vertical {{ subcontrol-position: top; "
        f"image: url({_scrollbar_arrow_path('up', 'rest')}); }} "
        f"QScrollBar::add-line:vertical {{ subcontrol-position: bottom; "
        f"image: url({_scrollbar_arrow_path('down', 'rest')}); }} "
        f"QScrollBar[hoverArrows=true]::sub-line:vertical {{ image: url({_scrollbar_arrow_path('up', 'hover')}); }} "
        f"QScrollBar[hoverArrows=true]::add-line:vertical {{ image: url({_scrollbar_arrow_path('down', 'hover')}); }} "
        f"QScrollBar::sub-line:vertical:pressed {{ image: url({_scrollbar_arrow_path('up', 'pressed')}); }} "
        f"QScrollBar::add-line:vertical:pressed {{ image: url({_scrollbar_arrow_path('down', 'pressed')}); }} "
        f"QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical {{ "
        f"background: none; }} "
        f"QScrollBar:horizontal {{ background: transparent; height: {size}px; "
        f"margin: 0px {size}px 2px {size}px; }} "
        f"QScrollBar::handle:horizontal {{ background: {BORDER}; min-width: {handle_min}px; "
        f"border-radius: {radius}px; }} "
        f"QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal {{ "
        f"width: {size}px; background: transparent; border: none; "
        f"border-radius: {radius}px; subcontrol-origin: margin; }} "
        f"QScrollBar::sub-line:horizontal {{ subcontrol-position: left; "
        f"image: url({_scrollbar_arrow_path('left', 'rest')}); }} "
        f"QScrollBar::add-line:horizontal {{ subcontrol-position: right; "
        f"image: url({_scrollbar_arrow_path('right', 'rest')}); }} "
        f"QScrollBar[hoverArrows=true]::sub-line:horizontal {{ image: url({_scrollbar_arrow_path('left', 'hover')}); }} "
        f"QScrollBar[hoverArrows=true]::add-line:horizontal {{ image: url({_scrollbar_arrow_path('right', 'hover')}); }} "
        f"QScrollBar::sub-line:horizontal:pressed {{ image: url({_scrollbar_arrow_path('left', 'pressed')}); }} "
        f"QScrollBar::add-line:horizontal:pressed {{ image: url({_scrollbar_arrow_path('right', 'pressed')}); }} "
        f"QScrollBar::add-page:horizontal, QScrollBar::sub-page:horizontal {{ "
        f"background: none; }} "
        f"QScrollBar::corner {{ background: transparent; }}"
    )



URL_PATTERN = re.compile(r"https?://\S+|www\.\S+")

# Punctuation/wrapping characters commonly stuck to a pasted URL that aren't part of it
# (e.g. "check this out: https://example.com/video, nice right?" or "(https://x.com)")
_URL_TRAILING_CHARS = ".,;:!?)]}\"'"


# Whether a candidate string is actually a well-formed http(s) URL (has both a scheme
# and a host) rather than some other pasted text that merely looked URL-ish
def _is_valid_url(candidate):
    parsed = urllib.parse.urlparse(candidate)
    return parsed.scheme in ("http", "https") and bool(parsed.netloc)


# Pull only genuine http(s) URLs out of pasted text, trimming trailing punctuation picked
# up by the regex and normalizing "www." matches to a full https:// URL. Anything that
# isn't an actual link (plain words, file paths, etc.) is silently ignored.
def _extract_urls(text):
    urls = []
    for candidate in URL_PATTERN.findall(text):
        candidate = candidate.rstrip(_URL_TRAILING_CHARS)
        if not candidate:
            continue
        if candidate.lower().startswith("www."):
            candidate = f"https://{candidate}"
        if _is_valid_url(candidate):
            urls.append(candidate)
    return urls

# A pasted URL is treated as a playlist (expanded into a folder of links) rather than a
# single link when its path is the dedicated "/playlist" endpoint with a "list=" id -
# this deliberately excludes "watch?v=...&list=..." links, which are single videos that
# merely happen to carry playlist context
PLAYLIST_PATH_MARKER = "playlist"

# YouTube channel URLs - "/@handle", "/channel/UC...", "/c/name", or "/user/name" -
# optionally followed by a tab like "/videos" or "/streams". These list many videos
# just like a playlist does, so they're expanded into a folder the same way.
_YOUTUBE_HOSTS = ("youtube.com", "www.youtube.com", "m.youtube.com")
_CHANNEL_PATH_PATTERN = re.compile(
    r"^/(?:@[^/]+|channel/[^/]+|c/[^/]+|user/[^/]+)(?:/(?:videos|streams|shorts|playlists))?/?$",
    re.IGNORECASE,
)


# Whether a pasted URL should be expanded into a folder of its playlist entries
def _is_playlist_url(url):
    parsed = urllib.parse.urlparse(url)
    query = urllib.parse.parse_qs(parsed.query)
    if PLAYLIST_PATH_MARKER in parsed.path.lower() and bool(query.get("list")):
        return True
    if parsed.netloc.lower() in _YOUTUBE_HOSTS and _CHANNEL_PATH_PATTERN.match(parsed.path):
        return True
    return False


# Whether a pasted URL is specifically a channel link (as opposed to a playlist)-
# used to warn when one lands in the Default profile instead of a dedicated Channel
# profile, which is what actually supports tracking/refreshing new uploads.
def _is_channel_url(url):
    parsed = urllib.parse.urlparse(url)
    return parsed.netloc.lower() in _YOUTUBE_HOSTS and bool(_CHANNEL_PATH_PATTERN.match(parsed.path))


# Stricter check used specifically when creating a "Channel" profile: the channel's
# "/videos" or "/shorts" tab URL, e.g. "https://www.youtube.com/@name/videos" or
# "https://www.youtube.com/channel/UC.../videos" or ".../@name/shorts". Unlike
# _is_playlist_url (which also accepts the bare channel URL or other tabs), this
# requires one of these two tabs specifically, since that's what gets re-fetched
# on every "Refresh".
_CHANNEL_VIDEOS_PATH_PATTERN = re.compile(
    r"^/(?:@[^/]+|channel/[^/]+|c/[^/]+|user/[^/]+)/(?:videos|shorts)/?$", re.IGNORECASE,
)


# True if url is a YouTube channel's /videos listing page (as opposed to a
# single video, playlist, etc.)
def _is_channel_videos_url(url):
    parsed = urllib.parse.urlparse((url or "").strip())
    if parsed.scheme not in ("http", "https"):
        return False
    if parsed.netloc.lower() not in _YOUTUBE_HOSTS:
        return False
    return bool(_CHANNEL_VIDEOS_PATH_PATTERN.match(parsed.path))


# Quality dropdown entries mapped to a max-height cap used to build the yt-dlp -f
# selector. Order matches the combo box's display order.
QUALITY_HEIGHTS = {
    "144p": 144,
    "240p": 240,
    "360p": 360,
    "480p": 480,
    "720p": 720,
    "1080p": 1080,
    "1440p (2K)": 1440,
    "2160p (4K)": 2160,
}
QUALITY_AUDIO_ONLY = "Audio only"
QUALITY_BEST = "Best available"


# Build the yt-dlp -f/-S arguments for the chosen quality tier. A hard [height<=N]
# filter breaks on vertical videos (Shorts): their "height" field is the long
# dimension, so e.g. a 1080x1920 Short gets wrongly excluded by a height<=1080 cap,
# and yt-dlp errors out with "Requested format is not available" instead of falling
# back. -S "res:N" avoids this: yt-dlp's "res" sort key is rotation-independent
# (based on the shorter dimension) and only ever re-orders candidates - it can't
# fail to match anything the way a [height<=N] filter can.
def _format_args_for_quality(quality):
    if quality == QUALITY_AUDIO_ONLY:
        return ["-f", "bestaudio/best"]
    args = ["-f", "bestvideo*+bestaudio/best"]
    height = QUALITY_HEIGHTS.get(quality)
    if height is not None:
        args += ["-S", f"res:{height}"]
    return args

# Custom QTreeWidgetItem data roles: raw (unnumbered) text, folder flag, and forced-quality override
RAW_TEXT_ROLE = Qt.UserRole + 1
IS_FOLDER_ROLE = Qt.UserRole + 2
FORCED_QUALITY_ROLE = Qt.UserRole + 3
# The link's actual URL, kept separate from RAW_TEXT_ROLE once probing rewrites the display text
URL_ROLE = Qt.UserRole + 4
# Whether the link's last probe attempt failed, used by _NoFocusRectDelegate to force the yellow color
PROBE_FAILED_ROLE = Qt.UserRole + 5
# Whether the link/folder was manually disabled via the context menu. This is tracked
# as our own data role rather than via QTreeWidgetItem.setDisabled()/Qt::ItemIsEnabled,
# because Qt's built-in disabled state also blocks selection and mouse interaction -
# which would make a disabled row impossible to right-click and re-enable.
LINK_DISABLED_ROLE = Qt.UserRole + 6
# Stable unique identifier assigned to each link when it's first added, used to
# detect duplicate URLs already present in the tree
LINK_UUID_ROLE = Qt.UserRole + 7
# Local filesystem path of the link's downloaded thumbnail image, if any
THUMBNAIL_PATH_ROLE = Qt.UserRole + 8
# Uploader/channel name and upload date ("YYYYMMDD" from yt-dlp) from the last probe,
# used for the sidebar preview only - the tree row text is unaffected by these
CHANNEL_ROLE = Qt.UserRole + 9
UPLOAD_DATE_ROLE = Qt.UserRole + 10
SIZE_ROLE = Qt.UserRole + 11
# Last known download progress (0-100 int), or None if never downloaded. Persisted
# to disk so a completed/partial percentage survives an app restart.
DOWNLOAD_PROGRESS_ROLE = Qt.UserRole + 12
# Whether a link has a pending "Force quality" change that hasn't been re-probed yet.
# Set when the quality is forced, cleared once the link's next probe attempt completes
# (success or failure), and reflected as a "[Force Quality]" prefix on the row meanwhile.
FORCE_QUALITY_PENDING_ROLE = Qt.UserRole + 13
# Seconds remaining on a link's retry cooldown after it has exhausted its download
# retries, or None/0 if it isn't currently cooling down. Set/ticked down by the
# retry-timeout QTimer and shown as a "[Ns] - " prefix on the row meanwhile.
DOWNLOAD_TIMEOUT_ROLE = Qt.UserRole + 14
# Absolute path to the file yt-dlp actually wrote for this link, captured from its
# own output once a download finishes. None if never downloaded (or the path
# couldn't be parsed out of yt-dlp's log). Used to relocate the file on disk when
# the link is dragged into/out of a folder in the tree.
DOWNLOAD_PATH_ROLE = Qt.UserRole + 15
# Extensions treated as playable video files for double-click "open in media player".
VIDEO_FILE_EXTENSIONS = {
    ".mp4", ".mkv", ".webm", ".mov", ".avi", ".flv", ".wmv", ".m4v",
    ".mpg", ".mpeg", ".ts", ".3gp",
}
# A link's fixed 1-based position in the playlist it was expanded from (the order
# yt-dlp reported, i.e. the uploader's order) - set once when the playlist folder is
# created and never touched again, so re-sorting the folder in the tree doesn't
# change it. None for links that didn't come from a playlist.
PLAYLIST_INDEX_ROLE = Qt.UserRole + 16
# Marks a synthetic, non-selectable "Load N more..." row inserted in place of a run
# of not-yet-built sibling items (see LINKS_LOAD_BATCH_SIZE below). Clicking it swaps
# itself out for the next batch of real items, plus a fresh sentinel if any remain.
IS_LOAD_MORE_ROLE = Qt.UserRole + 17
# The still-unbuilt sibling node dicts (same shape as items.json "children"/"items"
# entries) a load-more sentinel is standing in for.
LOAD_MORE_NODES_ROLE = Qt.UserRole + 18
# The plain probed title (no quality/size prefix, unlike RAW_TEXT_ROLE) - used
# wherever a clean link name is needed outside the tree display, e.g. the
# "Downloading: <name>" log line.
TITLE_ROLE = Qt.UserRole + 19
# The video's runtime ("M:SS"/"H:MM:SS") from the last probe, or "" if yt-dlp didn't
# report one (e.g. a livestream) - used for the sidebar preview only, like CHANNEL_ROLE
# and UPLOAD_DATE_ROLE above.
DURATION_ROLE = Qt.UserRole + 20
# Whether the link's last probe failure looked like a members-only/join-to-watch
# video (detected from the probe's error text - see _on_probe_error) rather than a
# generic/transient probe failure. Colored red (MEMBERS_ONLY_COLOR) instead of the
# usual yellow, and skipped automatically by the download queue (_start_downloads)
# since there's nothing downloadable to retry.
MEMBERS_ONLY_ROLE = Qt.UserRole + 21
# Exact upload instant as a Unix timestamp (seconds) from yt-dlp's "timestamp" field,
# when it reports one - unlike UPLOAD_DATE_ROLE this has minute (not just day)
# precision, which is what a Sub Group's "Number downloads by upload order" setting
# sorts on (see _subgroup_upload_order_map). None if yt-dlp didn't report one.
UPLOAD_TIMESTAMP_ROLE = Qt.UserRole + 22
# A Sub Group channel folder's own quality override (e.g. "720p"), letting
# different channels in the same sub group probe/download at different qualities.
# Mirrors that channel's "quality" entry in the profile's "channels" metadata (the
# actual source of truth - see save_profile_metadata/_sync_subgroup_folder_qualities)
# so it survives the folder being torn down and rebuilt. None/unset for any folder
# that isn't a Sub Group channel folder, in which case the global Quality setting
# applies as usual (see _quality_for_item).
FOLDER_QUALITY_ROLE = Qt.UserRole + 23
# Whether the link is a "Skip" placeholder: kept in the tree (and so still counts
# toward a Refresh's "already known" video-ID set - see
# _existing_channel_video_ids/_existing_channel_video_ids_in_folder - so a Refresh
# correctly stops there and never re-adds it) but excluded from downloading
# (_start_downloads/_update_download_button) and from numbering
# (_renumber_siblings/_subgroup_upload_order_map). For a video the user never wants
# downloaded - an unrelated upload, a duplicate, a teaser - that still needs to
# occupy its real position/date so refresh and ordering stay correct around it.
LINK_SKIPPED_ROLE = Qt.UserRole + 24
# Set on a link that was already completed (DOWNLOAD_PROGRESS_ROLE == 100) at the
# moment "Reset numbering" (the empty-space context menu action, Sub Group profiles
# only - see _reset_subgroup_numbering) was last used: permanently excludes it from
# numbering (_renumber_siblings/_subgroup_upload_order_map), same treatment as a
# skipped link, so whatever hasn't downloaded yet renumbers down to start at 1
# again. Cleared if the link is later manually Reset for re-download (see
# _reset_selected), letting it re-enter the numbering sequence.
LINK_NUMBERING_RESET_ROLE = Qt.UserRole + 25
# Set (to True) on a profile_list separator row added by _add_profile_list_separator
# so _ProfileListSeparatorDelegate knows to paint a divider line for it instead of
# normal item text. Unrelated to the URL-tree roles above - this is a different
# widget/model entirely, just continuing the same numbering for tidiness.
PROFILE_LIST_SEPARATOR_ROLE = Qt.UserRole + 26
# The playlist URL a folder was expanded from (see _on_playlist_expanded), kept
# around so a "Playlist" profile's Refresh can re-fetch that same listing later
# and append any videos added to it since. None for a folder that wasn't created
# from a playlist link (a manually-created folder, a Channel/Sub Group folder, etc).
PLAYLIST_SOURCE_URL_ROLE = Qt.UserRole + 27
# How many sibling items (top-level, or children of one folder) are materialized into
# real QTreeWidgetItems at once when loading from disk. Building thousands of items
# synchronously on startup freezes the UI, so any run longer than this is loaded in
# pages instead, with a clickable "Load N more..." row standing in for the rest.
LINKS_LOAD_BATCH_SIZE = 500

# Fixed (theme-independent) color used to flag a link whose probe failed
PROBE_FAILED_COLOR = "#e0b400"

# Fixed (theme-independent) color used to flag a link that finished downloading (100%)
DOWNLOAD_COMPLETE_COLOR = "#3ecf5f"

# Fixed (theme-independent) color used to flag a link currently on a retry cooldown
DOWNLOAD_TIMEOUT_COLOR = "#e0b400"

# Fixed (theme-independent) color used to flag a members-only video (probe failed
# because it needs a channel membership to watch, not a transient error)
MEMBERS_ONLY_COLOR = "#e05c5c"

# Fixed (theme-independent) color used to flag a link marked "Skip" (a placeholder
# that's kept for refresh/ordering purposes but never downloaded)
SKIPPED_COLOR = "#5a9bd4"

# Substring (matched case-insensitively) that shows up in yt-dlp's error text for a
# members-only/"join this channel" video across every platform we've seen it on -
# used to tell that case apart from a generic/transient probe failure. See
# _on_probe_error.
MEMBERS_ONLY_ERROR_HINT = "member"


APP_NAME = "ytdlp-links"
APP_VERSION = "2026.08.17"

# API endpoint this app's own releases will be checked against, mirroring
# _YTDLP_LATEST_RELEASE_URL/_FFMPEG_LATEST_RELEASE_URL below. Left unset for now -
# the About tab's app-version check treats that the same as a failed lookup
# ("could not check for updates") until this is filled in.
APP_LATEST_RELEASE_URL = None


# Ask wherever this app's releases end up published (see APP_LATEST_RELEASE_URL)
# for the latest released version ("tag_name"), optionally through proxy. Returns
# None if the URL isn't configured yet, or on any network/HTTP/parsing failure -
# same "couldn't check" contract as get_latest_ytdlp_version/get_latest_ffmpeg_version.
def get_latest_app_version(timeout=8, proxy=None):
    if not APP_LATEST_RELEASE_URL:
        return None
    handlers = [urllib.request.ProxyHandler({"http": proxy, "https": proxy})] if proxy else []
    opener = urllib.request.build_opener(*handlers)
    request = urllib.request.Request(
        APP_LATEST_RELEASE_URL, headers={"Accept": "application/vnd.github+json"},
    )
    try:
        with opener.open(request, timeout=timeout) as resp:
            data = json.loads(resp.read().decode("utf-8", errors="replace"))
    except (OSError, urllib.error.URLError, ValueError, json.JSONDecodeError):
        return None
    tag = data.get("tag_name") if isinstance(data, dict) else None
    return tag.strip() if isinstance(tag, str) and tag.strip() else None


# Name of the local socket used to detect an already-running instance of the app -
# see _try_activate_running_instance/_listen_for_other_instances/main. Just needs
# to be unique to this app, not anything user-facing.
SINGLE_INSTANCE_KEY = f"{APP_NAME}-single-instance-lock"
# How long to wait for an already-running instance to answer before assuming
# there isn't one after all - kept short since this only blocks startup, and a
# real running instance answers almost instantly.
SINGLE_INSTANCE_CONNECT_TIMEOUT_MS = 500


# Try to reach an already-running instance of the app via its local socket
# (SINGLE_INSTANCE_KEY). If one answers, ask it to raise/focus its window (see
# _listen_for_other_instances) and return True so main() can exit instead of
# opening a second instance. Returns False if nothing answers - either no other
# instance is running, or a stale socket was left behind by one that crashed
# (see QLocalServer.removeServer in _listen_for_other_instances, which cleans
# that up for the *next* instance to actually start listening).
def _try_activate_running_instance():
    socket = QLocalSocket()
    socket.connectToServer(SINGLE_INSTANCE_KEY)
    if not socket.waitForConnected(SINGLE_INSTANCE_CONNECT_TIMEOUT_MS):
        return False
    socket.write(b"activate")
    socket.waitForBytesWritten(SINGLE_INSTANCE_CONNECT_TIMEOUT_MS)
    socket.disconnectFromServer()
    return True


# Start listening on this instance's local socket so a later launch of the app can
# detect us (_try_activate_running_instance) and ask us to raise/focus our window
# instead of opening a second instance alongside us. Removes any stale socket left
# behind by a previous crash before listening (QLocalServer.listen() otherwise
# fails if one is already on disk - Unix-only; Windows named pipes don't have this
# issue, so removeServer() is a harmless no-op there). Returns the QLocalServer,
# which the caller must keep a live reference to for as long as the app runs.
def _listen_for_other_instances(window):
    QLocalServer.removeServer(SINGLE_INSTANCE_KEY)
    server = QLocalServer()
    server.listen(SINGLE_INSTANCE_KEY)

    # Another instance is asking us to take over - raise and focus our window
    def _on_new_connection():
        socket = server.nextPendingConnection()
        if socket is not None:
            socket.disconnectFromServer()
        if window.isMinimized():
            window.showNormal()
        window.raise_()
        window.activateWindow()

    server.newConnection.connect(_on_new_connection)
    return server


# Settings and saved-links files live inside the active profile's folder
SETTINGS_FILENAME = "settings.json"
LINKS_FILENAME = "links.json"
# Subfolder (inside the active profile's folder) where per-link thumbnail images are cached
THUMBNAILS_DIRNAME = "thumbnails"

# Per-profile metadata (name/type/channel_url) - stored inside each profile's own
# folder, right alongside that profile's links.json/settings.json/thumbnails, so the
# whole folder is self-contained: copy it anywhere (a backup drive, another machine,
# back into exe/profiles/ under a new name) to back up or restore that one profile,
# without any separate registry file to keep in sync.
PROFILE_METADATA_FILENAME = "profile.json"

# Small pointer file kept at the top level (next to the executable/script), since it
# has to be read before we know which profile folder to even look at. Unlike
# PROFILE_METADATA_FILENAME, this holds no profile data of its own - just the name of
# whichever profile was last active - so it's fine that it doesn't travel along when
# a profile folder gets copied elsewhere.
LAST_PROFILE_FILENAME = "last_profile.json"

# Old, pre-{PROFILE_METADATA_FILENAME}-per-folder registry format: a single combined
# file (also at the top level) listing every profile's name/type/channel_url plus
# which one was last active. Only read once, to migrate existing installs onto the
# per-profile-folder scheme above, then removed.
LEGACY_PROFILES_FILENAME = "profiles.json"

# Subfolder (next to the executable/script) under which each profile gets its own
# folder, named after the profile itself
PROFILES_DIRNAME = "profiles"

# Subfolder (next to the executable/script) that plugins must be browsed from.
# App-wide (not per-profile), since a plugin isn't tied to any one profile.
PLUGINS_DIRNAME = "plugins"
# Top-level file (next to the executable/script) listing which plugins (by
# filename, inside PLUGINS_DIRNAME) are currently added
PLUGINS_ENABLED_FILENAME = "plugins.json"
# A .py file is only accepted as a plugin if its first line is exactly this comment
PLUGIN_MARKER_COMMENT = "# for ytdlp-links"

DEFAULT_PROFILE_NAME = "Default"
# Profile "type" is a label describing what kind of URL(s) a profile is meant to
# hold; offered as a choice when creating a new profile. The Default profile has
# no type of its own.
PROFILE_TYPES = ["Generic video", "Generic file", "Playlist", "Channel", "Sub Group"]


# Open the OS file browser at `path`. If `path` is an existing file, the containing
# folder opens with that file selected/highlighted (matching what a right-click ->
# "Show in folder" does in most apps); if it's a directory (or the file no longer
# exists), the folder itself just opens with nothing selected. Falls back to plain
# QDesktopServices.openUrl (which can only open a folder, never select a file inside
# it) on platforms/setups where the OS-specific reveal command isn't available.
# Returns True if something was launched, False if even the fallback failed.
def _reveal_path(path):
    p = Path(path)
    is_file = p.is_file()
    try:
        if sys.platform.startswith("win"):
            if is_file:
                # The trailing comma after /select is significant to explorer.exe's
                # (undocumented) argument parsing - splitting it into its own list
                # element like this is what makes that survive subprocess escaping.
                subprocess.Popen(["explorer", "/select,", str(p)])
            else:
                subprocess.Popen(["explorer", str(p)])
            return True
        if sys.platform == "darwin":
            if is_file:
                subprocess.Popen(["open", "-R", str(p)])
            else:
                subprocess.Popen(["open", str(p)])
            return True
        # Linux/other Unix: no universal "reveal and select" command. Try file
        # managers that support one, in rough order of how common they are;
        # fall through to just opening the containing folder unselected.
        if is_file:
            for args in (["nautilus", "--select", str(p)], ["dolphin", "--select", str(p)],
                         ["nemo", str(p)], ["thunar", str(p)]):
                if shutil.which(args[0]):
                    subprocess.Popen(args)
                    return True
    except OSError:
        pass
    target_dir = p if p.is_dir() else p.parent
    return QDesktopServices.openUrl(QUrl.fromLocalFile(str(target_dir)))


# Best-effort resolution of the current Windows user's real "Downloads" folder
# via the shell's known-folder API, honoring any redirection the user (or e.g.
# OneDrive) has set up - unlike just assuming it's ~/Downloads, which can be
# wrong once a folder's been relocated. Returns None on failure (non-Windows,
# or the API call itself failing) so the caller can fall back to a plain
# Path.home() / "Downloads" guess.
def _windows_known_downloads_dir():
    if sys.platform != "win32":
        return None
    try:
        import ctypes

        class GUID(ctypes.Structure):
            _fields_ = [
                ("Data1", ctypes.c_ulong),
                ("Data2", ctypes.c_ushort),
                ("Data3", ctypes.c_ushort),
                ("Data4", ctypes.c_ubyte * 8),
            ]

        # FOLDERID_Downloads - has no legacy CSIDL, only available via
        # SHGetKnownFolderPath (Vista+)
        FOLDERID_Downloads = GUID(
            0x374DE290, 0x123F, 0x4565,
            (ctypes.c_ubyte * 8)(0x91, 0x64, 0x39, 0xC4, 0x92, 0x5E, 0x46, 0x7B),
        )

        buf = ctypes.c_wchar_p()
        result = ctypes.windll.shell32.SHGetKnownFolderPath(
            ctypes.byref(FOLDERID_Downloads), 0, None, ctypes.byref(buf)
        )
        if result == 0 and buf.value:
            path = buf.value
            ctypes.windll.ole32.CoTaskMemFree(buf)
            return path
    except Exception:
        pass
    return None


# Default "Download location" for a profile that's never had one explicitly
# set - the OS's normal Downloads folder, rather than leaving the field blank
# (which used to just block downloads with "no download location is set"
# until the user manually browsed to one).
def _default_download_dir():
    known = _windows_known_downloads_dir()
    if known:
        return known
    return str(Path.home() / "Downloads")


# Path to icon.ico, used ONLY for the direct-WinAPI taskbar icon fix below
# (_force_windows_taskbar_icon) - kept separate from _app_icon_path()/icon.png,
# which is what Qt itself uses for the title bar. Loaded via the raw Win32
# LoadImageW call, not through Qt's QImage decoders, so - unlike going through
# QIcon - this has no dependency on PySide6's ICO imageformat plugin being
# present/loadable in the frozen build.
def _app_icon_ico_path():
    if getattr(sys, "frozen", False):
        bundled = Path(getattr(sys, "_MEIPASS", "")) / "icon.ico"
        if bundled.is_file():
            return bundled
        return _app_dir() / "icon.ico"
    return _app_dir() / "icon.ico"


# Directly sets the taskbar button's icon via the Win32 API, bypassing Qt's
# higher-level setWindowIcon() entirely.
#
# Why this is needed: on Windows, the taskbar button's icon comes from
# WM_SETICON (and, for how some shell paths look it up, the window class's
# GCLP_HICON) on the native HWND - NOT from whatever Qt-level QIcon was set
# via QApplication.setWindowIcon()/QWidget.setWindowIcon(). Those Qt calls do
# reliably drive the *title bar* icon (a separate Windows code path), but in
# PyInstaller onefile builds the taskbar button is frequently created by
# Explorer before/without ever picking up the inherited icon, leaving a
# generic icon that only gets refreshed if some other event (e.g. a second
# top-level window appearing, as observed when switching profiles) makes
# Windows re-query it. Setting WM_SETICON explicitly, right after the window
# is shown and a real HWND exists, avoids relying on that timing/propagation
# at all.
#
# No-op (silently) on any failure or on non-Windows platforms - this is a
# cosmetic fix, never worth failing app startup over.
def _force_windows_taskbar_icon(win):
    if sys.platform != "win32":
        return
    try:
        import ctypes
        from ctypes import wintypes

        ico_path = _app_icon_ico_path()
        if not ico_path.is_file():
            return

        user32 = ctypes.windll.user32
        user32.LoadImageW.restype = wintypes.HICON
        user32.LoadImageW.argtypes = [
            wintypes.HINSTANCE,
            wintypes.LPCWSTR,
            wintypes.UINT,
            ctypes.c_int,
            ctypes.c_int,
            wintypes.UINT,
        ]
        user32.SendMessageW.restype = ctypes.c_void_p
        user32.SendMessageW.argtypes = [
            wintypes.HWND,
            wintypes.UINT,
            wintypes.WPARAM,
            wintypes.LPARAM,
        ]

        IMAGE_ICON = 1
        LR_LOADFROMFILE = 0x00000010
        WM_SETICON = 0x0080
        ICON_SMALL = 0
        ICON_BIG = 1
        SM_CXICON = 11
        SM_CYICON = 12
        SM_CXSMICON = 49
        SM_CYSMICON = 50
        GCLP_HICON = -14

        hwnd = wintypes.HWND(int(win.winId()))
        path_str = str(ico_path)

        cx_small = user32.GetSystemMetrics(SM_CXSMICON)
        cy_small = user32.GetSystemMetrics(SM_CYSMICON)
        cx_big = user32.GetSystemMetrics(SM_CXICON)
        cy_big = user32.GetSystemMetrics(SM_CYICON)

        hicon_small = user32.LoadImageW(None, path_str, IMAGE_ICON, cx_small, cy_small, LR_LOADFROMFILE)
        hicon_big = user32.LoadImageW(None, path_str, IMAGE_ICON, cx_big, cy_big, LR_LOADFROMFILE)

        if hicon_small:
            user32.SendMessageW(hwnd, WM_SETICON, ICON_SMALL, hicon_small)
        if hicon_big:
            user32.SendMessageW(hwnd, WM_SETICON, ICON_BIG, hicon_big)
            # Some shell code paths (notably taskbar button creation) read the
            # window class's icon rather than the per-window WM_SETICON value,
            # so set that too, for good measure.
            if ctypes.sizeof(ctypes.c_void_p) == 8:
                user32.SetClassLongPtrW(hwnd, GCLP_HICON, hicon_big)
            else:
                user32.SetClassLongW(hwnd, GCLP_HICON, hicon_big)

        # Keep the HICON handles reachable for the app's lifetime - not
        # strictly required (they're not Python-GC'd since they're bare
        # ctypes ints), but avoids any doubt about them being cleaned up
        # from under the window.
        win._taskbar_hicons = (hicon_small, hicon_big)
    except Exception:
        pass


# Path to icon.png used as the window/taskbar icon. When frozen into a
# --onefile exe, PyInstaller extracts bundled data files (added via --add-data)
# into a temp folder at sys._MEIPASS at runtime, so we look there first; when
# running as a plain script, it's just next to this file. Just a path; the
# caller is responsible for handling the file not being there (see main()).
#
# Deliberately .png, not .ico: PySide6's ICO reader lives in a separate
# imageformats plugin (qico.dll) that PyInstaller onefile builds frequently
# fail to load at runtime (plugin search path doesn't line up with the
# onefile temp extraction folder), silently producing a null QIcon - i.e. no
# icon anywhere, title bar included. PNG decoding is built directly into
# QtGui itself, so it has no such plugin-loading dependency.
def _app_icon_path():
    if getattr(sys, "frozen", False):
        bundled = Path(getattr(sys, "_MEIPASS", "")) / "icon.png"
        if bundled.is_file():
            return bundled
        return _app_dir() / "icon.png"
    return _app_dir() / "icon.png"


# Persistent, writable folder holding this app's own copies of yt-dlp and ffmpeg,
# kept next to the exe/script (like everything else this app writes - see
# _app_dir()) as "ytdlp-bin". Nothing ships here from inside the .exe anymore -
# it's populated by the About tab's updater (or the startup "missing binaries"
# prompt - see _check_required_binaries_on_startup), or by the user dropping the
# executables in by hand.
def _bundled_bin_dir():
    path = _app_dir() / "ytdlp-bin"
    path.mkdir(parents=True, exist_ok=True)
    return path


# Full path to this app's own copy of a bundled executable (yt-dlp or ffmpeg)
def _bundled_bin_path(name):
    return _bundled_bin_dir() / name


# Filename of the vendored yt-dlp executable for the current platform (yt-dlp's
# own release naming for its standalone builds)
def _ytdlp_bin_name():
    return "yt-dlp.exe" if sys.platform == "win32" else "yt-dlp"


# Full path to this app's own copy of yt-dlp, in its persistent ytdlp-bin folder
# (see _bundled_bin_dir). Not shipped inside the .exe - the app expects it to be
# fetched (see update_ytdlp/_download_ytdlp_fresh), fetched via the About tab's
# updater, or placed there by hand.
def _ytdlp_bin_path():
    return _bundled_bin_path(_ytdlp_bin_name())


# The command used to invoke yt-dlp everywhere in this app: always this app's own
# copy in its ytdlp-bin folder (see _ytdlp_bin_path) - never a system/PATH lookup,
# since the whole point is that this app carries and manages its own copy rather
# than depending on anything separately installed.
def _ytdlp_cmd():
    return str(_ytdlp_bin_path())


# Filename of the vendored ffmpeg executable for the current platform
def _ffmpeg_bin_name():
    return "ffmpeg.exe" if sys.platform == "win32" else "ffmpeg"


# Full path to this app's own copy of ffmpeg, passed to yt-dlp via
# --ffmpeg-location (see download_url) rather than relying on yt-dlp's own PATH/
# same-directory-as-itself auto-discovery, so it's not dependent on anything
# separately installed on the system either. Same "not shipped in the .exe -
# fetched or placed by hand" story as _ytdlp_bin_path above.
def _ffmpeg_bin_path():
    return _bundled_bin_path(_ffmpeg_bin_name())


# Strip characters that aren't safe to use as a folder name, so an arbitrary
# profile name typed by the user can always be turned into a real folder
def _sanitize_profile_name(name):
    cleaned = re.sub(r'[\\/:*?"<>|]', "", (name or "")).strip()
    # Strip leading/trailing dots so a name that's entirely dots (".", "..", "...")
    # can never end up as its own path component - without this, a profile named
    # ".." would resolve to the *parent* of the profiles folder (i.e. the app's own
    # directory), so creating it would overwrite the Default profile's files and
    # deleting it would rmtree the whole app folder. Dots elsewhere in the name
    # (e.g. "My..Profile") are left untouched since those aren't special to the
    # filesystem.
    cleaned = cleaned.strip(".")
    return cleaned or DEFAULT_PROFILE_NAME


# Full path to the small last-active-profile pointer file
def _last_profile_file_path():
    return _app_dir() / LAST_PROFILE_FILENAME


# Name of the profile that was last active, or None if there's no pointer file yet
def load_last_profile_name():
    data = _load_json_file(_last_profile_file_path())
    return data.get("last_profile") if isinstance(data, dict) else None


# Persist which profile is currently active. This is the only profile-related file
# ever written next to the executable/script itself - it holds no profile data, just
# a name, so it's fine that it doesn't travel with a profile folder that gets copied
# elsewhere for backup/restore.
def save_last_profile_name(name):
    _save_json_file(_last_profile_file_path(), {"last_profile": name})


# Where a given (non-Default) profile's folder would live, without creating it.
# Used to check whether a profile still actually exists on disk.
def _profile_dir_path(name):
    return _app_dir() / PROFILES_DIRNAME / _sanitize_profile_name(name)


# Folder (created on demand) holding a given profile's links/settings/thumbnails.
# The Default profile's data lives directly next to the executable/script (matching
# where a single-profile version of this app would have kept it); every other
# profile gets its own folder under exe/profiles/<name>.
def _dir_for_profile(name):
    if name == DEFAULT_PROFILE_NAME:
        return _app_dir()
    path = _profile_dir_path(name)
    try:
        path.mkdir(parents=True, exist_ok=True)
    except OSError:
        pass
    return path


# Folder that plugins must be browsed from, next to the executable/script -
# app-wide, shared across every profile. NOT created here: plugins are
# currently just a placeholder feature, so this only returns the path rather
# than creating it on disk - callers that read from it (startup load, list
# refresh) have nothing to gain from the folder existing, and creating an
# empty "plugins" folder next to the exe with nothing to put in it yet is
# just clutter. _on_browse_plugin_clicked() creates it on demand instead,
# right before it's actually needed as a QFileDialog target.
def _plugins_dir():
    return _app_dir() / PLUGINS_DIRNAME


# Full path to the top-level file listing which plugins are currently added
def _plugins_enabled_file_path():
    return _app_dir() / PLUGINS_ENABLED_FILENAME


# List of plugin filenames (inside PLUGINS_DIRNAME) that were previously added
def load_enabled_plugins():
    data = _load_json_file(_plugins_enabled_file_path())
    if isinstance(data, dict) and isinstance(data.get("enabled"), list):
        return [str(name) for name in data["enabled"]]
    return []


# Persist the list of currently-added plugin filenames
def save_enabled_plugins(names):
    _save_json_file(_plugins_enabled_file_path(), {"enabled": list(names)})


# A .py file only counts as a plugin if its first line is exactly the marker
# comment - this is what lets Browse... tell a real plugin apart from any other
# .py file that happens to sit in the plugins folder
def _is_valid_plugin_file(path):
    try:
        with path.open("r", encoding="utf-8") as f:
            first_line = f.readline()
    except OSError:
        return False
    return first_line.strip() == PLUGIN_MARKER_COMMENT


# Load a profile's own profile.json (name/type/channel_url) from inside its folder,
# without creating anything. Returns None if the folder or file doesn't exist.
def load_profile_metadata(name):
    folder = _app_dir() if name == DEFAULT_PROFILE_NAME else _profile_dir_path(name)
    data = _load_json_file(folder / PROFILE_METADATA_FILENAME)
    return data if isinstance(data, dict) else None


# Write a profile's own profile.json into its folder, creating the folder if needed.
# "channels" is only meaningful for a "Sub Group" profile: a list of
# {"name": ..., "url": ...} dicts, one per tracked channel - each "name" doubles as
# that channel's own top-level folder name in the tree (see _get_or_create_named_folder).
# "number_by_upload_order" is also Sub Group-only: when set, downloads across every
# channel in the group are numbered and pulled in oldest-upload-first order instead
# of top-to-bottom tree order (see _subgroup_upload_order_map).
def save_profile_metadata(name, ptype, channel_url, channels=None, number_by_upload_order=False):
    _save_json_file(_dir_for_profile(name) / PROFILE_METADATA_FILENAME, {
        "name": name, "type": ptype, "channel_url": channel_url, "channels": channels,
        "number_by_upload_order": bool(number_by_upload_order),
    })


# Build the full list of known profiles purely from what's on disk: the Default
# profile's own profile.json (in the app folder itself) plus every subfolder of
# exe/profiles/ that has its own profile.json. There's no separate registry that can
# go stale - a profile deleted (or a backup copied back in) from outside the program
# is picked up automatically the next time this is called.
def _discover_profiles():
    profiles = []

    default_meta = load_profile_metadata(DEFAULT_PROFILE_NAME) or {}
    profiles.append({
        "name": DEFAULT_PROFILE_NAME,
        "type": default_meta.get("type"),
        "channel_url": default_meta.get("channel_url"),
        "channels": default_meta.get("channels"),
        "number_by_upload_order": bool(default_meta.get("number_by_upload_order")),
    })

    profiles_root = _app_dir() / PROFILES_DIRNAME
    if profiles_root.is_dir():
        for entry in sorted(profiles_root.iterdir(), key=lambda e: e.name.lower()):
            if not entry.is_dir():
                continue
            meta = _load_json_file(entry / PROFILE_METADATA_FILENAME)
            if not isinstance(meta, dict) or not meta.get("name"):
                continue
            profiles.append({
                "name": meta["name"],
                "type": meta.get("type"),
                "channel_url": meta.get("channel_url"),
                "channels": meta.get("channels"),
                "number_by_upload_order": bool(meta.get("number_by_upload_order")),
            })
    return profiles


# One-time upgrade path: fold an old combined profiles.json registry (if one is
# still sitting next to the executable/script from a previous version) into each
# profile's own profile.json, then remove it, so existing installs move onto the
# per-profile-folder scheme without losing their profiles' type/channel_url.
def _migrate_legacy_profiles_file():
    legacy_path = _app_dir() / LEGACY_PROFILES_FILENAME
    legacy = _load_json_file(legacy_path)
    if isinstance(legacy, dict):
        entries = legacy.get("profiles")
        if isinstance(entries, list):
            for p in entries:
                if not isinstance(p, dict) or not p.get("name"):
                    continue
                name = p["name"]
                folder = _app_dir() if name == DEFAULT_PROFILE_NAME else _profile_dir_path(name)
                if folder.is_dir() and not (folder / PROFILE_METADATA_FILENAME).exists():
                    save_profile_metadata(name, p.get("type"), p.get("channel_url"))
        last = legacy.get("last_profile")
        if last:
            save_last_profile_name(last)
    try:
        legacy_path.unlink()
    except OSError:
        pass


# Name of the profile whose links/settings/thumbnails are currently active. Every
# path helper below reads this, so switching profiles just means changing it (via
# set_current_profile) and reloading - the helpers themselves don't need to change.
_current_profile_name = DEFAULT_PROFILE_NAME


# Switch which profile's data the path helpers above resolve against
def set_current_profile(name):
    global _current_profile_name
    _current_profile_name = name


# Folder holding the currently active profile's data
def _profile_dir():
    return _dir_for_profile(_current_profile_name)


# Full path to the active profile's settings JSON file
def _settings_file_path():
    return _profile_dir() / SETTINGS_FILENAME


# Full path to the active profile's saved-links JSON file
def _links_file_path():
    return _profile_dir() / LINKS_FILENAME


# Directory (created on demand) where the active profile's downloaded thumbnails
# are cached, one per link UUID
def _thumbnails_dir():
    path = _profile_dir() / THUMBNAILS_DIRNAME
    try:
        path.mkdir(parents=True, exist_ok=True)
    except OSError:
        pass
    return path


# Recursively collect every "url" field out of a list of raw saved-node dicts
# (the items.json "children"/"items" shape) - used to check for duplicates against
# links still pending inside a "Load more" sentinel, not yet built as tree items
def _collect_urls_from_nodes(nodes):
    urls = set()
    for node in nodes:
        if not isinstance(node, dict):
            continue
        if node.get("is_folder"):
            urls.update(_collect_urls_from_nodes(node.get("children") or []))
        else:
            url = node.get("url")
            if url:
                urls.add(url)
    return urls


# Recursively collect every "download_path" field out of a list of raw saved-node
# dicts (the links.json "children"/"items" shape) - used when deleting a profile
# to also remove its downloaded video files from disk
def _collect_download_paths_from_nodes(nodes):
    paths = []
    for node in nodes:
        if not isinstance(node, dict):
            continue
        if node.get("is_folder"):
            paths.extend(_collect_download_paths_from_nodes(node.get("children") or []))
        else:
            path = node.get("download_path")
            if path:
                paths.append(path)
    return paths


# Existing cached thumbnail file for a link UUID, if any (matched regardless of extension)
def _existing_thumbnail_path(link_uuid):
    if not link_uuid:
        return None
    return next(_thumbnails_dir().glob(f"{link_uuid}.*"), None)


# Download url's bytes to dest_path, optionally through proxy ("scheme://host:port").
# Restricted to http(s): urllib's default opener also happily follows "file://" (and
# "ftp://") URLs, and url here ultimately comes from a remote site's own metadata
# (see download_thumbnail) - without this check, a malicious/compromised page could
# hand back a "thumbnail" of "file:///etc/passwd" (or some other local file this
# process can read) and have its contents silently written into the thumbnails
# folder. Raises ValueError for anything else, which download_thumbnail already
# treats as an ordinary failed download.
def _download_to_file(url, dest_path, timeout, proxy=None):
    if urllib.parse.urlparse(url).scheme not in ("http", "https"):
        raise ValueError(f"refusing to download non-http(s) url: {url!r}")
    handlers = [urllib.request.ProxyHandler({"http": proxy, "https": proxy})] if proxy else []
    opener = urllib.request.build_opener(*handlers)
    with opener.open(url, timeout=timeout) as resp:
        dest_path.write_bytes(resp.read())


# Download a link's thumbnail (if thumbnail_url is present) into thumbnails/<uuid><ext>,
# replacing any previously cached thumbnail for that UUID. Failures are non-fatal since
# a missing thumbnail shouldn't stop a probe from succeeding.
def download_thumbnail(thumbnail_url, link_uuid, timeout, proxy=None):
    if not thumbnail_url or not link_uuid:
        return None
    remove_thumbnail(link_uuid)
    ext = Path(urllib.parse.urlparse(thumbnail_url).path).suffix
    if not ext or len(ext) > 5:
        ext = ".jpg"
    dest = _thumbnails_dir() / f"{link_uuid}{ext}"
    try:
        _download_to_file(thumbnail_url, dest, timeout, proxy)
    except (OSError, ValueError, urllib.error.URLError):
        return None
    return dest.as_posix()


# Delete the cached thumbnail file for a link UUID, if one exists
def remove_thumbnail(link_uuid):
    path = _existing_thumbnail_path(link_uuid)
    if path is not None:
        path.unlink(missing_ok=True)


# Load JSON data from the given path, returning None if missing or invalid
def _load_json_file(path):
    try:
        with path.open("r", encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError):
        return None
    return data


# Write JSON data to the given path atomically via a temp file + rename
def _save_json_file(path, data):
    try:
        fd, tmp_name = tempfile.mkstemp(dir=str(path.parent), prefix=".tmp-", suffix=".tmp")
        try:
            with open(fd, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
            Path(tmp_name).replace(path)
        except Exception:
            Path(tmp_name).unlink(missing_ok=True)
            raise
    except OSError:
        pass


# Load saved settings from disk, returning None if missing or invalid
def load_settings_file():
    data = _load_json_file(_settings_file_path())
    return data if isinstance(data, dict) else None


# Write settings to disk atomically
def save_settings_file(data):
    _save_json_file(_settings_file_path(), data)


# Load the saved URL/folder tree from disk, returning None if missing or invalid
def load_links_file():
    data = _load_json_file(_links_file_path())
    return data if isinstance(data, dict) else None


# Write the URL/folder tree to disk atomically
def save_links_file(data):
    _save_json_file(_links_file_path(), data)


# Run "yt-dlp -j <url>" (optionally through a proxy) using the given quality setting,
# and pull out the title, resolution, and file size of the format that would actually
# be selected/produced. Container/codec choice is left to yt-dlp's own defaults.
# is_file=True (a "Generic file" profile) skips the -f/-S quality args entirely, since
# those only make sense for a video/audio extraction and a plain file has no such
# "formats" to choose between - yt-dlp just probes whatever the URL serves as-is.
def probe_url(url, timeout, quality, proxy=None, process_holder=None, is_file=False):
    command = [_ytdlp_cmd(), "--no-playlist", "--no-warnings", "-j"]
    # yt-dlp autodetects the system/env proxy when --proxy is omitted entirely, so
    # an explicit "no proxy" state has to pass --proxy "" to force a direct connection
    command += ["--proxy", proxy or ""]
    if not is_file:
        command += _format_args_for_quality(quality)
    # "--" forces everything after it to be treated as a positional argument,
    # never as an option - without it, a url that happens to start with "-"
    # (e.g. a corrupted/tampered saved link, or a malformed entry from a
    # playlist/channel listing) would be parsed by yt-dlp's own argument
    # parser as a flag instead of a download target.
    command += ["--", url]
    # Popen (rather than subprocess.run) so process_holder can hand the running
    # process back to the caller, letting a cancelled probe be killed outright
    # instead of running to completion for nothing.
    proc = subprocess.Popen(
        command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        encoding="utf-8", errors="replace", env=_subprocess_env(),
        **_subprocess_no_window_kwargs(),
    )
    if process_holder is not None:
        process_holder(proc)
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.communicate()
        raise
    if proc.returncode != 0:
        message = (stderr or "probe failed").strip().splitlines()
        raise RuntimeError(message[-1] if message else "probe failed")
    stdout_lines = stdout.splitlines()
    if not stdout_lines:
        # yt-dlp exited 0 but printed nothing to probe - treat as a failed probe
        # instead of letting IndexError propagate uncaught (ProbeTask.run() only
        # catches RuntimeError/ValueError/JSONDecodeError, so an uncaught IndexError
        # here would silently kill the worker thread and leave the item stuck
        # showing "probing" forever with no error surfaced).
        raise RuntimeError("probe failed: yt-dlp returned no output")
    data = json.loads(stdout_lines[0])
    title = data.get("title") or url
    if is_file:
        # No video/audio format was requested, so "height" (or its absence, which
        # would otherwise read as "audio") says nothing meaningful about a plain
        # file - leave it out of the result rather than show a misleading quality.
        quality = ""
    else:
        height = data.get("height")
        quality = f"{height}p" if height else "audio"
    size_bytes = data.get("filesize") or data.get("filesize_approx")
    size = _format_size(size_bytes) if size_bytes else "?"
    channel = data.get("uploader") or data.get("channel") or ""
    upload_date = _format_upload_date(data.get("upload_date"))
    # "timestamp" is yt-dlp's exact upload instant (Unix seconds), when the site
    # exposes one - unlike "upload_date" (day-only), this preserves minute-level
    # ordering, needed for a Sub Group's "Number downloads by upload order" setting.
    upload_timestamp = data.get("timestamp") or data.get("release_timestamp")
    duration = _format_duration(data.get("duration"))
    return {
        "title": title, "quality": quality, "size": size,
        "thumbnail_url": data.get("thumbnail"),
        "channel": channel, "upload_date": upload_date,
        "upload_timestamp": upload_timestamp, "duration": duration,
    }



# Environment for every yt-dlp subprocess we launch. Without this, yt-dlp (a Python
# program itself) picks its *own* stdout encoding from the system locale - on Windows
# that's commonly cp1252, which can't represent characters yt-dlp substitutes into
# sanitized filenames (e.g. the fullwidth colon "：" it uses in place of ":" on
# Windows-illegal filenames). yt-dlp's console output then silently drops those
# characters (errors="ignore") rather than raising, so the "[download] Destination:"
# line we parse for the final file path comes out missing characters that the actual
# file on disk has - the file downloads and is named correctly, but our recorded path
# no longer matches it, and later actions (e.g. double-click to open) report the file
# as not found. Forcing PYTHONIOENCODING/PYTHONUTF8 makes yt-dlp emit the *exact* same
# UTF-8 text it uses for the real filename, so what we parse always matches disk.
def _subprocess_env():
    env = os.environ.copy()
    env["PYTHONIOENCODING"] = "utf-8"
    env["PYTHONUTF8"] = "1"
    return env


# Extra kwargs for every yt-dlp subprocess.Popen/run call, to stop Windows from
# briefly flashing a console window for the child process. yt-dlp is a
# console-subsystem program, so even though *our* process is built with
# --windowed, Windows still pops up a (very brief) console for yt-dlp itself
# unless explicitly told not to via CREATE_NO_WINDOW. This is a no-op on
# non-Windows platforms, where the flag doesn't exist.
def _subprocess_no_window_kwargs():
    if sys.platform == "win32":
        return {"creationflags": subprocess.CREATE_NO_WINDOW}
    return {}


# Run "yt-dlp --version" and return the reported version string, or None if
# yt-dlp isn't on PATH or the call fails for any other reason
def get_ytdlp_version():
    try:
        result = subprocess.run(
            [_ytdlp_cmd(), "--version"], capture_output=True, text=True,
            encoding="utf-8", errors="replace", env=_subprocess_env(), timeout=5,
            **_subprocess_no_window_kwargs(),
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if result.returncode != 0:
        return None
    output = result.stdout.strip()
    return output.splitlines()[0] if output else None


# GitHub API endpoint reporting yt-dlp's latest published release
_YTDLP_LATEST_RELEASE_URL = "https://api.github.com/repos/yt-dlp/yt-dlp/releases/latest"
# Human-browsable page for the same release - opened in the default browser from
# the "yt-dlp" link in the startup missing-binaries popup (see
# _on_missing_binaries_link_clicked) so someone who'd rather grab it by hand has
# somewhere to go.
_YTDLP_RELEASES_PAGE_URL = "https://github.com/yt-dlp/yt-dlp/releases/latest"
# Human-browsable page for yt-dlp's nightly builds - linked from the "nightly
# builds" hint in the same popup, for anyone who wants to drop one in by hand
# instead of using a stable release.
_YTDLP_NIGHTLY_RELEASES_PAGE_URL = "https://github.com/yt-dlp/yt-dlp-nightly-builds/releases"


# Ask GitHub for yt-dlp's latest released version ("tag_name", e.g. "2025.08.01"),
# optionally through proxy ("scheme://host:port"). Returns None on any network,
# HTTP, or parsing failure - the About tab treats that as "couldn't check", not
# as "no update available".
def get_latest_ytdlp_version(timeout=8, proxy=None):
    handlers = [urllib.request.ProxyHandler({"http": proxy, "https": proxy})] if proxy else []
    opener = urllib.request.build_opener(*handlers)
    request = urllib.request.Request(
        _YTDLP_LATEST_RELEASE_URL, headers={"Accept": "application/vnd.github+json"},
    )
    try:
        with opener.open(request, timeout=timeout) as resp:
            data = json.loads(resp.read().decode("utf-8", errors="replace"))
    except (OSError, urllib.error.URLError, ValueError, json.JSONDecodeError):
        return None
    tag = data.get("tag_name")
    return tag.strip() if isinstance(tag, str) and tag.strip() else None


# Run "yt-dlp -U" to have this app's own copy of yt-dlp (see _ytdlp_cmd) update
# itself in place, or - if there's no copy there yet, e.g. a fresh install, since
# this app no longer ships yt-dlp inside its own .exe - fetch one fresh instead
# (see _download_ytdlp_fresh). Returns (success, output) where output is the
# combined stdout/stderr text yt-dlp printed (or a fresh-download status message).
# success is False if the update/download fails or times out, or yt-dlp exits
# non-zero.
#
# Since this always runs the app's own standalone binary copy (never a pip
# install), yt-dlp's normal self-update mechanism just works - no pip fallback
# needed, and the update only ever touches this app's private copy, never
# anything else installed on the system.
#
# If given, log(str) is called once per step (command about to run, then what it
# printed) so the caller can stream progress live instead of only finding out once
# everything's finished - see YtdlpUpdateTask.
def update_ytdlp(timeout=180, log=None, proxy=None):
    if log is None:
        log = lambda _msg: None

    if not _ytdlp_bin_path().is_file():
        log("yt-dlp not found - downloading a fresh copy")
        return _download_ytdlp_fresh(timeout=timeout, log=log, proxy=proxy)

    log("Running: yt-dlp -U")
    try:
        result = subprocess.run(
            [_ytdlp_cmd(), "-U"], capture_output=True, text=True,
            encoding="utf-8", errors="replace", env=_subprocess_env(), timeout=timeout,
            **_subprocess_no_window_kwargs(),
        )
    except OSError as e:
        log(f"yt-dlp update failed to start: {e}")
        return False, f"yt-dlp update failed to start: {e}"
    except subprocess.TimeoutExpired:
        log("yt-dlp update timed out")
        return False, "yt-dlp update timed out"
    output = (result.stdout + result.stderr).strip()
    log(output or "(no output)")
    log("yt-dlp self-update succeeded" if result.returncode == 0 else "yt-dlp self-update failed")
    return result.returncode == 0, output


# Run "ffmpeg -version" (this app's own bundled copy - see _ffmpeg_bin_path) and
# return the reported version string (e.g. "N-122010-g1d47ae65bf-20251205"), or
# None if the bundled copy is missing or the call fails for any other reason
def get_ffmpeg_version():
    if not _ffmpeg_bin_path().is_file():
        return None
    try:
        result = subprocess.run(
            [str(_ffmpeg_bin_path()), "-version"], capture_output=True, text=True,
            encoding="utf-8", errors="replace", env=_subprocess_env(), timeout=5,
            **_subprocess_no_window_kwargs(),
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if result.returncode != 0:
        return None
    output = result.stdout.strip()
    first_line = output.splitlines()[0] if output else ""
    match = re.match(r"ffmpeg version (\S+)", first_line)
    return match.group(1) if match else None


# GitHub API endpoint for yt-dlp's own ffmpeg builds - see
# https://github.com/yt-dlp/FFmpeg-Builds/releases/tag/latest. Unlike yt-dlp's own
# releases, this "latest" tag is a floating build with no meaningful version
# number of its own (its release name is just an auto-build timestamp), so what
# gets compared isn't the tag but the *build date* - see
# _ffmpeg_version_build_date/get_latest_ffmpeg_version below.
_FFMPEG_LATEST_RELEASE_URL = "https://api.github.com/repos/yt-dlp/FFmpeg-Builds/releases/tags/latest"
# Human-browsable page for the same release - opened in the default browser from
# the "ffmpeg" link in the startup missing-binaries popup, same idea as
# _YTDLP_RELEASES_PAGE_URL above.
_FFMPEG_RELEASES_PAGE_URL = "https://github.com/yt-dlp/FFmpeg-Builds/releases/tag/latest"


# Pull the "YYYYMMDD" build-date suffix off the end of an "ffmpeg -version" style
# version string (yt-dlp/FFmpeg-Builds bakes one in, e.g.
# "N-122010-g1d47ae65bf-20251205" -> "20251205"), or None if the string isn't in
# that shape (e.g. a differently-built ffmpeg with no date suffix) - in which case
# there's nothing meaningful to compare against the latest release's publish date.
def _ffmpeg_version_build_date(version):
    if not version:
        return None
    match = re.search(r"(\d{8})$", version)
    return match.group(1) if match else None


# What the About tab actually shows for the installed ffmpeg version. These
# builds' real version string is a wall of commit-count/git-hash noise
# ("N-126061-g1a2b3c4d5e-20260811") with no meaningful number of its own - the
# build date is the only part anyone can actually use, so that's all the UI
# shows ("2026-08-11"). Falls back to the raw string for a differently-built
# ffmpeg with no date suffix (see _ffmpeg_version_build_date), so nothing is
# silently hidden when there's no date to show instead.
def _ffmpeg_version_display(version):
    date = _ffmpeg_version_build_date(version)
    if date:
        return f"{date[0:4]}.{date[4:6]}.{date[6:8]}"
    return version


# Ask GitHub for the publish date of yt-dlp/FFmpeg-Builds' rolling "latest"
# release, as a "YYYYMMDD" string, optionally through proxy ("scheme://host:port").
# Returns None on any network, HTTP, or parsing failure - the About tab treats
# that as "couldn't check", not as "no update available", same contract as
# get_latest_ytdlp_version.
def get_latest_ffmpeg_version(timeout=8, proxy=None):
    handlers = [urllib.request.ProxyHandler({"http": proxy, "https": proxy})] if proxy else []
    opener = urllib.request.build_opener(*handlers)
    request = urllib.request.Request(
        _FFMPEG_LATEST_RELEASE_URL, headers={"Accept": "application/vnd.github+json"},
    )
    try:
        with opener.open(request, timeout=timeout) as resp:
            data = json.loads(resp.read().decode("utf-8", errors="replace"))
    except (OSError, urllib.error.URLError, ValueError, json.JSONDecodeError):
        return None
    published = data.get("published_at") or data.get("created_at") if isinstance(data, dict) else None
    if not isinstance(published, str):
        return None
    match = re.match(r"(\d{4})-(\d{2})-(\d{2})", published)
    return f"{match.group(1)}{match.group(2)}{match.group(3)}" if match else None


# Filename of the platform-appropriate asset published under yt-dlp/FFmpeg-Builds'
# "latest" release - a GPL build (matching what this app already bundles) for
# whichever OS/architecture it's currently running on
def _ffmpeg_release_asset_name():
    is_arm = platform.machine().lower() in ("arm64", "aarch64")
    if sys.platform == "win32":
        return f"ffmpeg-master-latest-{'winarm64' if is_arm else 'win64'}-gpl.zip"
    return f"ffmpeg-master-latest-{'linuxarm64' if is_arm else 'linux64'}-gpl.tar.xz"


# Whether target resolves to somewhere inside directory (or directory itself) -
# used by _extract_ffmpeg_binary to guard against a malicious archive entry (e.g.
# "../../../../some/file" or an absolute path) that would otherwise let
# extractall() write outside the intended destination folder ("zip slip"/"tar
# slip", CWE-22).
def _is_within_directory(directory, target):
    directory = Path(directory).resolve()
    target = Path(target).resolve()
    return directory == target or directory in target.parents


# Extract every member of archive (a ZipFile or TarFile) into dest_dir, first
# checking that every member's path - and, for tar entries, the target of any
# symlink/hardlink - actually resolves to somewhere inside dest_dir. Raises
# ValueError on the first entry that doesn't, without extracting anything from
# that entry onward. This is purely a safety check on top of extractall(); it
# doesn't change what a well-formed archive extracts to.
def _safe_extractall(archive, dest_dir):
    dest_dir = Path(dest_dir).resolve()
    is_tar = isinstance(archive, tarfile.TarFile)
    members = archive.getmembers() if is_tar else archive.infolist()
    for member in members:
        name = member.name if is_tar else member.filename
        target = dest_dir / name
        if not _is_within_directory(dest_dir, target):
            raise ValueError(f"refusing to extract unsafe archive path: {name!r}")
        if is_tar and (member.issym() or member.islnk()):
            link_target = Path(member.linkname)
            if not link_target.is_absolute():
                link_target = target.parent / link_target
            if not _is_within_directory(dest_dir, link_target):
                raise ValueError(
                    f"refusing to extract unsafe link in archive: {name!r} -> {member.linkname!r}"
                )
    archive.extractall(dest_dir)


# Unpack the given release archive (.zip or .tar.xz) into dest_dir, then return the
# path to the "ffmpeg"/"ffmpeg.exe" binary inside it (these builds nest everything
# under "<archive-root>/bin/"), or None if it can't be found
def _extract_ffmpeg_binary(archive_path, dest_dir):
    if str(archive_path).endswith(".zip"):
        with zipfile.ZipFile(archive_path) as archive:
            _safe_extractall(archive, dest_dir)
    else:
        with tarfile.open(archive_path) as archive:
            _safe_extractall(archive, dest_dir)
    matches = list(Path(dest_dir).rglob(_ffmpeg_bin_name()))
    return matches[0] if matches else None


# Download this app's own copy of ffmpeg fresh from yt-dlp/FFmpeg-Builds' "latest"
# release (see _FFMPEG_LATEST_RELEASE_URL/_ffmpeg_release_asset_name) and replace
# the bundled copy (_ffmpeg_bin_path) in place. Returns (success, output), same
# contract as update_ytdlp above.
#
# Unlike yt-dlp, ffmpeg has no built-in self-update mechanism, so this downloads
# and unpacks the whole release archive itself rather than shelling out to
# anything. If given, log(str) is called once per step so the caller can stream
# progress live - see FfmpegUpdateTask.
def _download_with_resume(opener, url, dest_path, headers, timeout, log, max_stalled_attempts=5):
    """Download `url` to `dest_path`, resuming via HTTP Range requests if the
    connection is cut short partway through (seen with some proxies/AV on
    large files, which close the socket cleanly instead of resetting it, so
    a plain copyfileobj() never raises and silently saves a partial file).

    Mirrors this app's link-download retry behavior (see
    `_download_retry_counts`): the attempt counter only tracks *consecutive*
    attempts that make no forward progress, and is reset to zero the moment
    an attempt manages to write more bytes than the last one - so a slow but
    steadily-progressing download (11 retries, 30, whatever) is always given
    another try, and only a genuinely stuck download (max_stalled_attempts in
    a row with zero bytes gained) gives up.

    Returns (content_type, expected_size). Raises OSError if it can't
    complete the download after `max_stalled_attempts` consecutive attempts
    with no progress.
    """
    content_type = ""
    expected_size = None
    last_error = None
    stalled_attempts = 0
    attempt = 0

    while stalled_attempts < max_stalled_attempts:
        attempt += 1
        have = dest_path.stat().st_size if dest_path.exists() else 0
        req_headers = dict(headers)
        want_resume = have > 0
        if want_resume:
            req_headers["Range"] = f"bytes={have}-"
            log(f"Resuming download at {have} bytes (attempt {attempt})…")

        try:
            req = urllib.request.Request(url, headers=req_headers)
            with opener.open(req, timeout=timeout) as resp:
                status = getattr(resp, "status", None) or resp.getcode()
                if status and status >= 400:
                    raise OSError(f"server returned HTTP {status}")
                content_type = resp.headers.get("Content-Type", "") if resp.headers else content_type
                cl = resp.headers.get("Content-Length") if resp.headers else None

                if status == 206:
                    # Server honored the Range request: Content-Length here is
                    # only the size of the *remainder*, so recover the true
                    # total from Content-Range ("bytes start-end/total").
                    cr = resp.headers.get("Content-Range") if resp.headers else None
                    if cr and "/" in cr:
                        total = cr.rsplit("/", 1)[-1]
                        if total.isdigit():
                            expected_size = int(total)
                    with open(dest_path, "ab") as f:
                        shutil.copyfileobj(resp, f)
                else:
                    # A plain 200 always carries the *whole* entity, whether
                    # or not we asked for a range (some servers/proxies just
                    # ignore Range). Content-Length here is already the total
                    # size - do not add `have` on top of it. Since we didn't
                    # get the partial content we resumed for, start the file
                    # over from scratch to avoid duplicating/corrupting data.
                    if cl and cl.isdigit():
                        expected_size = int(cl)
                    with open(dest_path, "wb") as f:
                        shutil.copyfileobj(resp, f)
        except OSError as e:
            last_error = e
            stalled_attempts += 1
            log(
                f"Download attempt {attempt} failed: {e} "
                f"(no-progress attempt {stalled_attempts}/{max_stalled_attempts})"
            )
            continue

        size = dest_path.stat().st_size if dest_path.exists() else 0
        if expected_size is not None and size < expected_size:
            last_error = OSError(
                f"connection closed early: got {size} of {expected_size} bytes"
            )
            if size > have:
                # Made forward progress since the last attempt (even though
                # this one still fell short of the target) - give it a fresh
                # run of attempts rather than counting toward the stall limit.
                stalled_attempts = 0
                log(f"Download attempt {attempt} incomplete but progressing: {last_error}")
            else:
                stalled_attempts += 1
                log(
                    f"Download attempt {attempt} made no progress: {last_error} "
                    f"(no-progress attempt {stalled_attempts}/{max_stalled_attempts})"
                )
            continue

        return content_type, expected_size

    raise last_error or OSError("download failed for an unknown reason")


# Fetch a brand-new copy of yt-dlp straight from its latest GitHub release (the
# platform-appropriate standalone binary, matching _ytdlp_bin_name - e.g.
# "yt-dlp.exe" on Windows, "yt-dlp" elsewhere) and install it as this app's own
# copy (_ytdlp_bin_path). Used by update_ytdlp when there's no existing copy to
# run "yt-dlp -U" against - i.e. a fresh install, since this app no longer ships
# yt-dlp inside its own .exe. Returns (success, output), same contract as
# update_ytdlp/update_ffmpeg. Mirrors update_ffmpeg's own fresh-download logic
# below, just without an archive to unpack - yt-dlp's release asset is the bare
# executable itself.
def _download_ytdlp_fresh(timeout=180, log=None, proxy=None):
    if log is None:
        log = lambda _msg: None

    asset_name = _ytdlp_bin_name()
    handlers = [urllib.request.ProxyHandler({"http": proxy, "https": proxy})] if proxy else []
    opener = urllib.request.build_opener(*handlers)
    # GitHub's API (and, on some networks, intermediate proxies) will reject or
    # mangle requests with no User-Agent at all, so always send one.
    common_headers = {"User-Agent": "Mozilla/5.0 (compatible; ytdlp-updater)"}

    log(f"Looking up latest yt-dlp release ({asset_name})…")
    request = urllib.request.Request(
        _YTDLP_LATEST_RELEASE_URL,
        headers={**common_headers, "Accept": "application/vnd.github+json"},
    )
    try:
        with opener.open(request, timeout=timeout) as resp:
            data = json.loads(resp.read().decode("utf-8", errors="replace"))
    except (OSError, urllib.error.URLError, ValueError, json.JSONDecodeError) as e:
        log(f"Failed to look up latest yt-dlp release: {e}")
        return False, f"Failed to look up latest yt-dlp release: {e}"

    asset_url = None
    for asset in (data.get("assets") or []) if isinstance(data, dict) else []:
        if isinstance(asset, dict) and asset.get("name") == asset_name:
            asset_url = asset.get("browser_download_url")
            break
    if not asset_url:
        log(f'Could not find a "{asset_name}" asset in the latest yt-dlp release')
        return False, f'Could not find a "{asset_name}" asset in the latest yt-dlp release'

    try:
        # dir=_app_temp_dir() keeps the download scratch space next to the
        # executable rather than the system-wide temp dir, same rationale as
        # update_ffmpeg's own use of it below.
        with tempfile.TemporaryDirectory(dir=str(_app_temp_dir())) as tmp_dir:
            tmp_path = Path(tmp_dir) / asset_name
            log(f"Downloading {asset_name}…")
            try:
                content_type, expected_size = _download_with_resume(
                    opener, asset_url, tmp_path, common_headers, timeout, log,
                )
            except OSError as e:
                log(f"yt-dlp download failed: {e}")
                return False, f"yt-dlp download failed: {e}"

            size = tmp_path.stat().st_size if tmp_path.exists() else 0
            if size == 0 or (expected_size is not None and size != expected_size):
                detail = f"got {size} of {expected_size if expected_size is not None else '?'} bytes"
                log(f"yt-dlp download did not produce a complete file ({detail})")
                return False, f"yt-dlp download did not produce a complete file ({detail})"

            log("Installing new yt-dlp…")
            dest = _ytdlp_bin_path()
            try:
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(tmp_path, dest)
                if sys.platform != "win32":
                    dest.chmod(dest.stat().st_mode | 0o111)  # carry over the +x bit
            except OSError as e:
                log(f"Failed to install new yt-dlp: {e}")
                return False, f"Failed to install new yt-dlp: {e}"
    except OSError as e:
        log(f"yt-dlp download failed: {e}")
        return False, f"yt-dlp download failed: {e}"

    log("yt-dlp install succeeded")
    return True, "yt-dlp install succeeded"


def update_ffmpeg(timeout=180, log=None, proxy=None):
    if log is None:
        log = lambda _msg: None

    asset_name = _ffmpeg_release_asset_name()
    handlers = [urllib.request.ProxyHandler({"http": proxy, "https": proxy})] if proxy else []
    opener = urllib.request.build_opener(*handlers)
    # GitHub's API (and, on some networks, intermediate proxies) will reject or
    # mangle requests with no User-Agent at all, so always send one.
    common_headers = {"User-Agent": "Mozilla/5.0 (compatible; ffmpeg-updater)"}

    log(f"Looking up latest ffmpeg release ({asset_name})…")
    request = urllib.request.Request(
        _FFMPEG_LATEST_RELEASE_URL,
        headers={**common_headers, "Accept": "application/vnd.github+json"},
    )
    try:
        with opener.open(request, timeout=timeout) as resp:
            data = json.loads(resp.read().decode("utf-8", errors="replace"))
    except (OSError, urllib.error.URLError, ValueError, json.JSONDecodeError) as e:
        log(f"Failed to look up latest ffmpeg release: {e}")
        return False, f"Failed to look up latest ffmpeg release: {e}"

    asset_url = None
    for asset in (data.get("assets") or []) if isinstance(data, dict) else []:
        if isinstance(asset, dict) and asset.get("name") == asset_name:
            asset_url = asset.get("browser_download_url")
            break
    if not asset_url:
        log(f'Could not find a "{asset_name}" asset in the latest ffmpeg release')
        return False, f'Could not find a "{asset_name}" asset in the latest ffmpeg release'

    try:
        # dir=_app_temp_dir() keeps the download/extraction scratch space next to
        # the executable rather than the system-wide temp dir, same rationale as
        # the icon cache above - see _app_temp_dir. Still auto-deleted on exit,
        # same as a plain TemporaryDirectory().
        with tempfile.TemporaryDirectory(dir=str(_app_temp_dir())) as tmp_dir:
            archive_path = Path(tmp_dir) / asset_name
            log(f"Downloading {asset_name}…")
            try:
                content_type, expected_size = _download_with_resume(
                    opener, asset_url, archive_path, common_headers, timeout, log,
                )
            except OSError as e:
                log(f"ffmpeg download failed: {e}")
                return False, f"ffmpeg download failed: {e}"

            # Sanity-check that what we saved actually is the archive we asked
            # for before handing it to zipfile/tarfile - this turns a cryptic
            # "File is not a zip file" into something that says *what* we
            # actually got instead. A magic-byte check alone isn't enough: a
            # truncated zip can still start with a valid-looking local file
            # header and only fail once zipfile looks for the central
            # directory record at the *end* of the file, so we additionally
            # compare the downloaded size against the server's declared
            # Content-Length and, for zips, use zipfile.is_zipfile() which
            # actually validates the end-of-central-directory record.
            size = archive_path.stat().st_size if archive_path.exists() else 0
            with open(archive_path, "rb") as f:
                head = f.read(256)

            problems = []
            if size == 0:
                problems.append("downloaded file is empty")
            if expected_size is not None and size != expected_size:
                problems.append(
                    f"downloaded {size} bytes but server reported "
                    f"Content-Length {expected_size} (truncated download)"
                )
            if asset_name.endswith(".zip"):
                if size and not zipfile.is_zipfile(archive_path):
                    problems.append("file is not a valid zip archive (bad or missing central directory)")
            else:
                if size and not head.startswith(b"\xfd7zXZ\x00"):
                    problems.append("file does not look like a valid archive")

            if problems:
                snippet = head.decode("utf-8", errors="replace").strip().replace("\n", " ")[:200]
                detail = "; ".join(problems)
                log(
                    f"ffmpeg download did not produce a valid archive: {detail} "
                    f"(content-type {content_type!r}, starts with: {snippet!r})"
                )
                return False, f"ffmpeg download did not produce a valid archive: {detail}"

            log("Extracting ffmpeg…")
            try:
                extracted = _extract_ffmpeg_binary(archive_path, tmp_dir)
            except (OSError, ValueError, zipfile.BadZipFile, tarfile.TarError) as e:
                log(f"ffmpeg extraction failed: {e}")
                return False, f"ffmpeg extraction failed: {e}"
            if extracted is None:
                log("Could not find the ffmpeg binary inside the downloaded archive")
                return False, "Could not find the ffmpeg binary inside the downloaded archive"

            log("Installing new ffmpeg…")
            dest = _ffmpeg_bin_path()
            try:
                shutil.copy2(extracted, dest)
                if sys.platform != "win32":
                    dest.chmod(dest.stat().st_mode | 0o111)  # carry over the +x bit
            except OSError as e:
                log(f"Failed to install new ffmpeg: {e}")
                return False, f"Failed to install new ffmpeg: {e}"
    except OSError as e:
        log(f"ffmpeg update failed: {e}")
        return False, f"ffmpeg update failed: {e}"

    log("ffmpeg self-update succeeded")
    return True, "ffmpeg self-update succeeded"


# Matches yt-dlp's default progress line, e.g. "[download]  12.3% of  50.00MiB at  1.20MiB/s ETA 00:30"
_DOWNLOAD_PROGRESS_RE = re.compile(r"\[download\]\s+([\d.]+)%")
_DOWNLOAD_SPEED_RE = re.compile(r"at\s+([\d.]+)(Ki|Mi|Gi)?B/s")
# Matches yt-dlp's own report of where it wrote/merged a file, e.g.
# '[download] Destination: /x/y.mp4', '[Merger] Merging formats into "/x/y.mp4"',
# '[ExtractAudio] Destination: /x/y.mp3'. Note "Destination" is followed by a colon
# but "Merging formats into" is not (yt-dlp's literal log format), hence the ":?".
# The last match wins (merge/extract steps run after the raw download and report
# the final combined/converted file).
_DOWNLOAD_DESTINATION_RE = re.compile(
    r'\[(?:download|Merger|ExtractAudio)\]\s+(?:Destination|Merging formats into):?\s+"?([^"\n]+)"?'
)
# Matches yt-dlp's "[download] /x/y.ext has already been downloaded" line - printed
# instead of a Destination line when the target file (per the "-o" template) already
# exists on disk, so yt-dlp skips re-downloading it outright. Needed because the
# output template below embeds each video's id specifically so this only ever
# triggers for a genuine repeat of the *same* video (see the comment on name_template
# in download_url) - when it does trigger, we still need the path out of this line so
# the caller can record where the already-downloaded file lives.
_DOWNLOAD_ALREADY_DONE_RE = re.compile(r"\[download\]\s+(.+?)\s+has already been downloaded")

# Matches the " [<id>]" uniqueness tag download_url()'s output template appends to
# every filename (see the comment on name_template below), so it can be stripped
# back off for the final on-disk name in _dedupe_download_filename.
_ID_TAG_RE = re.compile(r"^(.*) \[[^\[\]]*\]$")


# Convert a yt-dlp "at X(Ki|Mi|Gi)?B/s" match into a plain KB/s float
def _speed_match_to_kbps(match):
    value = float(match.group(1))
    unit = match.group(2)
    if unit == "Gi":
        return value * 1024 * 1024
    if unit == "Mi":
        return value * 1024
    if unit == "Ki":
        return value
    return value / 1024


# Matches the trailing " [<id>].<ext>" tag download_url()'s output template appends
# to every filename (see the comment on name_template there) - used by
# _recover_final_path to pull out just the id, which (unlike the rest of the
# filename) is always plain ASCII and safe from the console-encoding issue below.
_FINAL_PATH_ID_TAG_RE = re.compile(r"\[([\w-]+)\]\.[^.\\/]+$")


# yt-dlp's console output can occasionally come through with non-ASCII characters
# (e.g. a Cyrillic title) corrupted, due to console/pipe encoding mismatches on
# Windows - even though the file itself was written to disk with the correct name
# via the OS's own Unicode filesystem APIs, which aren't affected by console
# encoding at all. When that happens, a final_path built from that same corrupted
# text won't match the real file on disk, and the caller wrongly concludes nothing
# was downloaded. Recover by extracting the video id from the trailing " [id].ext"
# tag - always plain ASCII even when everything before it got mangled - and
# looking for the real file that ends with that same tag in dest_dir instead.
def _recover_final_path(dest_dir, reported_path):
    if reported_path and Path(reported_path).is_file():
        return reported_path
    if not reported_path:
        return reported_path
    id_match = _FINAL_PATH_ID_TAG_RE.search(reported_path)
    if not id_match:
        return reported_path
    tag = f"[{id_match.group(1)}]"
    try:
        candidates = [p for p in Path(dest_dir).iterdir() if p.is_file() and tag in p.name]
    except OSError:
        return reported_path
    if not candidates:
        return reported_path
    candidates.sort(key=lambda p: p.stat().st_mtime, reverse=True)
    return str(candidates[0])


# Run "yt-dlp <url>" as a real download (not just metadata probing) into dest_dir,
# using the same quality selection as probe_url; container/codec choice is left to
# yt-dlp's own defaults. Calls progress_callback(percent) and speed_callback(kbps) as
# yt-dlp reports them, and line_callback(text) with a ready-to-log
# "filename:  52.8% of   20.74MiB at    2.59MiB/s ETA 00:03" line each time the percent
# changes; blocks until the download finishes or errors. Raises RuntimeError on a
# non-zero exit code.
# is_file=True (a "Generic file" profile) switches this over to yt-dlp's plain file
# download path: no -f/-S quality args (there's no video/audio format to choose
# between - and forcing one would make yt-dlp reject a URL that isn't a video at
# all), and no ffmpeg requirement, since there's nothing here for it to merge.
def download_url(url, dest_dir, quality, retries, proxy=None,
                  progress_callback=None, speed_callback=None, process_holder=None,
                  playlist_index=None, ignore_title_pattern=None, line_callback=None,
                  is_file=False):
    # bestvideo+bestaudio (used for every quality except "Audio only") downloads video
    # and audio as two separate files and needs ffmpeg to merge them into one. Without
    # it, yt-dlp just prints a warning, keeps both fragment files on disk unmerged
    # (e.g. "...f160.mp4" + "...f251.webm"), and still exits 0 - which would otherwise
    # look like a successful, complete download. Fail loudly instead. None of this
    # applies to a plain generic-file download, so skip the check entirely there.
    if not is_file and not _ffmpeg_bin_path().is_file():
        raise RuntimeError(
            "Bundled ffmpeg not found - required to merge downloaded video/audio "
            "into a single file."
        )
    command = [_ytdlp_cmd(), "--no-playlist", "--no-warnings", "--newline"]
    if not is_file:
        command += ["--ffmpeg-location", str(_ffmpeg_bin_path())]
    command += ["--proxy", proxy or ""]
    if not is_file:
        command += _format_args_for_quality(quality)
    command += ["--retries", str(retries)]
    # Strip the caller's "Ignore pattern in title" regex out of the title *metadata*
    # before yt-dlp evaluates the "-o" template below, so the match never makes it
    # into the filename on disk in the first place - e.g. "name | promo text" becomes
    # "name" here, so %(title)s resolves to "name" and the file is written as
    # "name.webm" rather than "name | promo text.webm" that then gets renamed.
    if ignore_title_pattern:
        command += ["--replace-in-metadata", "title", ignore_title_pattern, ""]
    # %(id)s here isn't for display - it's what stops two different videos that
    # happen to share a title from colliding on the very same destination path.
    # yt-dlp's own "already downloaded" check is just "does this exact output path
    # exist on disk"; with a plain "%(title)s.%(ext)s" template, video #2's path is
    # identical to video #1's the moment their titles match, so yt-dlp sees video #1's
    # file already sitting there, prints "has already been downloaded", and skips
    # actually fetching video #2 - reported to us as an instant, successful download
    # even though nothing was transferred. Tagging the id onto the end guarantees two
    # different videos never share an output path, while a genuine repeat of the same
    # video (same id) still correctly resolves to its existing file and is skipped as
    # intended. The id tag is stripped back off (with any true title collision
    # de-duplicated as name_1, name_2, ...) once the file's actually on disk - see
    # _dedupe_download_filename in the GUI layer.
    name_template = (
        f"{playlist_index} - %(title)s [%(id)s].%(ext)s" if playlist_index
        else "%(title)s [%(id)s].%(ext)s"
    )
    command += ["-o", f"{dest_dir.rstrip('/')}/{name_template}"]
    # "--" forces the url to be treated as a positional argument, never as an
    # option - see probe_url's identical comment for why this matters.
    command += ["--", url]
    proc = subprocess.Popen(
        command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1,
        encoding="utf-8", errors="replace", env=_subprocess_env(),
        **_subprocess_no_window_kwargs(),
    )
    if process_holder is not None:
        process_holder(proc)
    last_percent = -1
    final_path = None
    try:
        for line in proc.stdout:
            stripped = line.strip()
            percent_match = _DOWNLOAD_PROGRESS_RE.search(line)
            if percent_match:
                percent = int(float(percent_match.group(1)))
                if percent != last_percent:
                    last_percent = percent
                    if progress_callback is not None:
                        progress_callback(percent)
                    if line_callback is not None:
                        # Swap yt-dlp's generic "[download]" tag for a tree-style
                        # arrow, since this is logged directly under the
                        # "Downloading: <name>" line it belongs to rather than
                        # needing to repeat the name itself.
                        tail = re.sub(r"^.*?\[download\]", "", line, count=1).strip()
                        line_callback(f"|__ {tail}")
                speed_match = _DOWNLOAD_SPEED_RE.search(line)
                if speed_match and speed_callback is not None:
                    speed_callback(_speed_match_to_kbps(speed_match))
            dest_match = _DOWNLOAD_DESTINATION_RE.search(line)
            if dest_match:
                final_path = dest_match.group(1).strip()
                if line_callback is not None:
                    line_callback(f"|__ {stripped}")
                continue
            already_match = _DOWNLOAD_ALREADY_DONE_RE.search(line)
            if already_match:
                final_path = already_match.group(1).strip()
                if line_callback is not None:
                    line_callback(f"|__ {stripped}")
            # Anything yt-dlp itself flags as a problem (ffmpeg missing/failing to
            # merge, a postprocessor erroring out, etc.) was previously swallowed
            # entirely here - it never reached progress_callback/line_callback, so a
            # failed merge just silently left final_path pointing at a fragment that
            # then got deleted, surfacing only as an opaque "no output file was
            # found" with no clue why. Surface it instead.
            elif not percent_match and stripped and re.search(r"error|warning", stripped, re.I):
                if line_callback is not None:
                    line_callback(f"|__ {stripped}")
    finally:
        proc.stdout.close()
    returncode = proc.wait()
    if returncode != 0:
        raise RuntimeError("download failed")
    return _recover_final_path(dest_dir, final_path)


# Reformat yt-dlp's "YYYYMMDD" upload_date string into "YYYY.MM.DD", or "" if missing/malformed
def _format_upload_date(raw_date):
    if not raw_date or len(raw_date) != 8 or not raw_date.isdigit():
        return ""
    return f"{raw_date[0:4]}.{raw_date[4:6]}.{raw_date[6:8]}"


# Render a yt-dlp "duration" (seconds, possibly a float) as "M:SS" or "H:MM:SS", or
# "" if missing/invalid (e.g. a livestream, which has no fixed duration)
def _format_duration(seconds):
    try:
        total = int(seconds)
    except (TypeError, ValueError):
        return ""
    if total < 0:
        return ""
    hours, remainder = divmod(total, 3600)
    minutes, secs = divmod(remainder, 60)
    if hours:
        return f"{hours}:{minutes:02d}:{secs:02d}"
    return f"{minutes}:{secs:02d}"


# Render a byte count as a short "NNmb"/"N.Ngb" label for the probe result display
def _format_size(num_bytes):
    mb = num_bytes / (1024 * 1024)
    if mb >= 1024:
        return f"{mb / 1024:.1f}gb"
    return f"{mb:.0f}mb"


# Parse a "_format_size()"-style string (e.g. "45mb", "1.2gb") back into a byte
# count; returns None for missing/unknown sizes (e.g. "?") so callers can skip them
def _parse_size_to_bytes(size_str):
    if not size_str:
        return None
    text = size_str.strip().lower()
    try:
        if text.endswith("gb"):
            return float(text[:-2]) * 1024 * 1024 * 1024
        if text.endswith("mb"):
            return float(text[:-2]) * 1024 * 1024
    except ValueError:
        return None
    return None


# Parse a "_format_duration()"-style string ("M:SS" or "H:MM:SS") back into a
# total-seconds int; returns None for missing/malformed durations (e.g. a
# livestream with no fixed length) so callers can skip them
def _parse_duration_to_seconds(duration_str):
    if not duration_str:
        return None
    parts = duration_str.strip().split(":")
    if len(parts) not in (2, 3):
        return None
    try:
        parts = [int(p) for p in parts]
    except ValueError:
        return None
    if len(parts) == 3:
        hours, minutes, secs = parts
    else:
        hours = 0
        minutes, secs = parts
    return hours * 3600 + minutes * 60 + secs


# Emit signal, silently dropping it instead of raising if the underlying Qt
# object it belongs to has already been destroyed. Every *Signals class below is a
# plain QObject with no parent, kept alive only by its owning QRunnable task's
# Python reference - if the app closes (or, on a Sub Group, a task is otherwise
# discarded) while that task is still running on a QThreadPool worker thread, the
# signals object can be torn down out from under it before run() reaches its
# emit() call, which PySide6 reports as "RuntimeError: Signal source has been
# deleted". There's nothing left listening in that case anyway - the GUI is
# already gone or on its way out - so the correct response is to drop the signal,
# not crash the worker thread on the way out.
def _safe_emit(signal, *args):
    try:
        signal.emit(*args)
    except RuntimeError:
        pass


# Cross-thread signal carrier for the About tab's yt-dlp update check
class YtdlpUpdateCheckSignals(QObject):
    # installed version (or None if yt-dlp isn't on PATH), latest version (or None
    # if the GitHub check failed) - both fetched here rather than on the GUI thread,
    # since "yt-dlp --version" is itself a subprocess call that can briefly block
    finished = Signal(object, object)


# Looks up the installed and latest yt-dlp versions on a worker thread, so neither
# the subprocess call nor the (possibly slow/offline) network call ever blocks the UI
class YtdlpUpdateCheckTask(QRunnable):
    # Stash the proxy to use for the version check and set up its signal carrier
    def __init__(self, proxy=None):
        super().__init__()
        self.proxy = proxy
        self.signals = YtdlpUpdateCheckSignals()

    # Off the GUI thread: read the installed version, then (if found) the latest
    # one, and report both
    def run(self):
        installed = get_ytdlp_version()
        latest = get_latest_ytdlp_version(proxy=self.proxy) if installed else None
        _safe_emit(self.signals.finished, installed, latest)


# Cross-thread signal carrier for the About tab's manual yt-dlp update
class YtdlpUpdateSignals(QObject):
    # One line of progress as the update proceeds (e.g. which command is about to
    # run, and what it printed), so the log shows each step live instead of just a
    # single message once everything's done - see update_ytdlp's log callback.
    step = Signal(str)
    # success, combined stdout/stderr from the whole update (all steps), and the
    # version now installed (fetched here for the same reason as
    # YtdlpUpdateCheckTask above)
    finished = Signal(bool, str, object)


# Runs "yt-dlp -U" (or a fresh download if missing - see update_ytdlp) on a
# worker thread, reporting progress via YtdlpUpdateSignals.step and the final
# result via .finished
class YtdlpUpdateTask(QRunnable):
    # Stash the proxy to use for a fresh-download lookup (see update_ytdlp) and
    # set up this update run's signal carrier
    def __init__(self, proxy=None):
        super().__init__()
        self.proxy = proxy
        self.signals = YtdlpUpdateSignals()

    # Off the GUI thread: perform the update and report success/output/new version
    def run(self):
        success, output = update_ytdlp(
            log=lambda msg: _safe_emit(self.signals.step, msg), proxy=self.proxy,
        )
        _safe_emit(self.signals.finished, success, output, get_ytdlp_version())


# Cross-thread signal carrier for the About tab's ffmpeg update check
class FfmpegUpdateCheckSignals(QObject):
    # installed version (or None if the bundled copy is missing), latest build date
    # (or None if the GitHub check failed) - see get_ffmpeg_version/get_latest_ffmpeg_version
    finished = Signal(object, object)


# Looks up the installed and latest ffmpeg versions on a worker thread, mirroring
# YtdlpUpdateCheckTask above
class FfmpegUpdateCheckTask(QRunnable):
    def __init__(self, proxy=None):
        super().__init__()
        self.proxy = proxy
        self.signals = FfmpegUpdateCheckSignals()

    def run(self):
        installed = get_ffmpeg_version()
        latest = get_latest_ffmpeg_version(proxy=self.proxy) if installed else None
        _safe_emit(self.signals.finished, installed, latest)


# Cross-thread signal carrier for the About tab's manual ffmpeg update
class FfmpegUpdateSignals(QObject):
    # One line of progress as the update proceeds - see update_ffmpeg's log callback
    step = Signal(str)
    # success, combined output, and the version now installed
    finished = Signal(bool, str, object)


# Downloads and installs the latest ffmpeg build on a worker thread, reporting
# progress via FfmpegUpdateSignals.step and the final result via .finished
class FfmpegUpdateTask(QRunnable):
    def __init__(self, proxy=None):
        super().__init__()
        self.proxy = proxy
        self.signals = FfmpegUpdateSignals()

    def run(self):
        success, output = update_ffmpeg(
            log=lambda msg: _safe_emit(self.signals.step, msg), proxy=self.proxy,
        )
        _safe_emit(self.signals.finished, success, output, get_ffmpeg_version())


# Cross-thread signal carrier for the About tab's app-version update check
class AppUpdateCheckSignals(QObject):
    # latest version (or None if the check couldn't be performed/failed) - see
    # get_latest_app_version
    finished = Signal(object)


# Looks up the latest published app version on a worker thread. There's no
# equivalent "update" task for the app itself yet - see get_latest_app_version.
class AppUpdateCheckTask(QRunnable):
    def __init__(self, proxy=None):
        super().__init__()
        self.proxy = proxy
        self.signals = AppUpdateCheckSignals()

    def run(self):
        latest = get_latest_app_version(proxy=self.proxy)
        _safe_emit(self.signals.finished, latest)


# Cross-thread signal carrier for a single probe task's result/error
class ProbeSignals(QObject):
    finished = Signal(object, dict)
    error = Signal(object, str)


# Runs one yt-dlp probe on a worker thread and reports back via ProbeSignals
# Shared cancel/process-tracking behavior for QRunnable tasks that shell out to a
# subprocess (yt-dlp). Provides cooperative cancellation: cancel() marks the task
# cancelled and kills the tracked subprocess if one is already running; _hold_process
# is handed to the underlying probe/download/fetch call as process_holder so it can
# record the subprocess once started (or get killed immediately if cancel() already
# ran first). Subclasses call _init_cancellation() from their __init__.
class CancellableTaskMixin:
    def _init_cancellation(self):
        self._cancelled = threading.Event()
        self._process = None
        self._process_lock = threading.Lock()

    # Called from the GUI thread to stop this task outright. Kills the yt-dlp
    # process if it's already running, and suppresses any signal run() would
    # otherwise emit once it unwinds.
    def cancel(self):
        self._cancelled.set()
        with self._process_lock:
            proc = self._process
        if proc is not None and proc.poll() is None:
            proc.kill()

    # Handed to the probe/download/fetch call as process_holder; records the running
    # process so cancel() can kill it, or kills it immediately if cancellation
    # already happened first.
    def _hold_process(self, proc):
        with self._process_lock:
            if self._cancelled.is_set():
                proc.kill()
                return
            self._process = proc


class ProbeTask(CancellableTaskMixin, QRunnable):
    # Stash everything probe_url needs, plus cancellation/process-tracking state
    def __init__(self, item, url, link_uuid, timeout, quality, proxy=None, is_file=False):
        super().__init__()
        self.item = item
        self.url = url
        self.link_uuid = link_uuid
        self.timeout = timeout
        self.quality = quality
        self.proxy = proxy
        self.is_file = is_file
        self.signals = ProbeSignals()
        self._init_cancellation()

    # Off the GUI thread: probe the url, download its thumbnail, and report back
    # (or report an error)
    def run(self):
        if self._cancelled.is_set():
            return
        try:
            info = probe_url(
                self.url, self.timeout, self.quality, self.proxy,
                process_holder=self._hold_process, is_file=self.is_file,
            )
        except FileNotFoundError:
            if not self._cancelled.is_set():
                _safe_emit(self.signals.error, self.item, "yt-dlp not found on PATH")
        except subprocess.TimeoutExpired:
            if not self._cancelled.is_set():
                _safe_emit(self.signals.error, self.item, "probe timed out")
        except (RuntimeError, ValueError, json.JSONDecodeError) as exc:
            if not self._cancelled.is_set():
                _safe_emit(self.signals.error, self.item, str(exc))
        else:
            if self._cancelled.is_set():
                return
            # Downloading the thumbnail here (still on the worker thread) keeps the UI
            # responsive; a failed/missing thumbnail must never fail the probe itself.
            info["thumbnail_path"] = download_thumbnail(
                info.get("thumbnail_url"), self.link_uuid, self.timeout, self.proxy,
            )
            if self._cancelled.is_set():
                return
            _safe_emit(self.signals.finished, self.item, info)


# Cross-thread signal carrier for a single download task's progress/result/error
class DownloadSignals(QObject):
    progress = Signal(object, int)
    speed = Signal(object, float)
    line = Signal(object, str)
    finished = Signal(object, object)
    error = Signal(object, str)


# Runs one real yt-dlp download on a worker thread and reports back via DownloadSignals
class DownloadTask(CancellableTaskMixin, QRunnable):
    # Stash everything download_url needs, plus cancellation/process-tracking state
    def __init__(self, item, url, dest_dir, quality, retries, proxy=None,
                 playlist_index=None, ignore_title_pattern=None, is_file=False):
        super().__init__()
        self.item = item
        self.url = url
        self.dest_dir = dest_dir
        self.quality = quality
        self.retries = retries
        self.proxy = proxy
        self.playlist_index = playlist_index
        self.ignore_title_pattern = ignore_title_pattern
        self.is_file = is_file
        self.signals = DownloadSignals()
        self._init_cancellation()

    # Relay a progress update, unless this task was cancelled
    def _on_progress(self, percent):
        if not self._cancelled.is_set():
            _safe_emit(self.signals.progress, self.item, percent)

    # Relay a speed reading, unless this task was cancelled
    def _on_speed(self, kbps):
        if not self._cancelled.is_set():
            _safe_emit(self.signals.speed, self.item, kbps)

    # Relay a raw output line, unless this task was cancelled
    def _on_line(self, text):
        if not self._cancelled.is_set():
            _safe_emit(self.signals.line, self.item, text)

    # Off the GUI thread: run the download and report the final path (or an error)
    def run(self):
        if self._cancelled.is_set():
            return
        try:
            final_path = download_url(
                self.url, self.dest_dir, self.quality,
                self.retries, self.proxy,
                progress_callback=self._on_progress, speed_callback=self._on_speed,
                process_holder=self._hold_process, playlist_index=self.playlist_index,
                ignore_title_pattern=self.ignore_title_pattern, line_callback=self._on_line,
                is_file=self.is_file,
            )
        except FileNotFoundError:
            if not self._cancelled.is_set():
                _safe_emit(self.signals.error, self.item, "yt-dlp not found on PATH")
        except RuntimeError as exc:
            if not self._cancelled.is_set():
                _safe_emit(self.signals.error, self.item, str(exc))
        else:
            if self._cancelled.is_set():
                return
            _safe_emit(self.signals.finished, self.item, final_path)


# How long to give yt-dlp to list a playlist's contents. Kept generous and independent of
# the per-link probing timeout, since a playlist listing can cover hundreds of entries.
PLAYLIST_FETCH_TIMEOUT = 300


# Run "yt-dlp --flat-playlist -J <url>" (optionally through a proxy) and pull out the
# playlist's title plus the webpage URL of each entry
def fetch_playlist(url, proxy=None, process_holder=None):
    command = [_ytdlp_cmd(), "--no-warnings", "--flat-playlist", "-J"]
    command += ["--proxy", proxy or ""]
    # "--" forces the url to be treated as a positional argument, never as an
    # option - see probe_url's identical comment for why this matters.
    command += ["--", url]
    # Popen (rather than subprocess.run) so process_holder can hand the running
    # process back to the caller, letting a cancelled listing be killed outright.
    proc = subprocess.Popen(
        command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        encoding="utf-8", errors="replace", env=_subprocess_env(),
        **_subprocess_no_window_kwargs(),
    )
    if process_holder is not None:
        process_holder(proc)
    try:
        stdout, stderr = proc.communicate(timeout=PLAYLIST_FETCH_TIMEOUT)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.communicate()
        raise
    if proc.returncode != 0:
        message = (stderr or "playlist fetch failed").strip().splitlines()
        raise RuntimeError(message[-1] if message else "playlist fetch failed")
    data = json.loads(stdout)
    title = data.get("title") or "Playlist"
    entries = []
    for entry in data.get("entries") or []:
        if not isinstance(entry, dict):
            continue
        entry_url = entry.get("webpage_url") or entry.get("url")
        if not entry_url:
            continue
        # --flat-playlist sometimes gives a bare video ID instead of a full URL
        if not entry_url.startswith(("http://", "https://")):
            entry_url = f"https://www.youtube.com/watch?v={entry_url}"
        entries.append(entry_url)
    return {"title": title, "entries": entries}


# Pull a single webpage URL out of one --flat-playlist -j entry dict, normalizing a
# bare video ID (which --flat-playlist sometimes gives instead of a full URL) into a
# full YouTube watch URL. Returns None if the entry has no usable URL.
def _entry_url_from_flat_entry(entry):
    entry_url = entry.get("webpage_url") or entry.get("url")
    if not entry_url:
        return None
    if not entry_url.startswith(("http://", "https://")):
        entry_url = f"https://www.youtube.com/watch?v={entry_url}"
    return entry_url


# Matches a YouTube video ID out of a watch/shorts/embed/youtu.be URL
_YOUTUBE_VIDEO_ID_IN_URL = re.compile(r"(?:v=|/shorts/|/embed/|youtu\.be/)([A-Za-z0-9_-]{11})")


# Pull the bare 11-character YouTube video ID out of a URL (or a bare ID string).
# Used to compare "is this the same video" reliably - unlike full URL strings, which
# can differ harmlessly between two mentions of the same video (webpage_url vs a
# raw id turned into a URL, extra query params like &t= or tracking params, etc).
# Returns None if no video ID can be found (e.g. a non-YouTube link).
def _youtube_video_id(url):
    if not url:
        return None
    if re.fullmatch(r"[A-Za-z0-9_-]{11}", url):
        return url
    match = _YOUTUBE_VIDEO_ID_IN_URL.search(url)
    return match.group(1) if match else None


# Video ID for one --flat-playlist -j entry dict. Prefers the entry's own "id" field
# (always the bare video ID yt-dlp extracted), falling back to parsing it out of
# webpage_url/url for the rare entry that omits "id".
def _channel_entry_video_id(entry):
    entry_id = entry.get("id")
    if entry_id and re.fullmatch(r"[A-Za-z0-9_-]{11}", entry_id):
        return entry_id
    return _youtube_video_id(entry.get("webpage_url") or entry.get("url") or "")


# Like fetch_playlist, but for a channel "Refresh": a channel's /videos listing is
# newest-first, and after the first refresh everything past the newest-known video is
# already in the tree. Rather than always waiting on "-J" (which makes yt-dlp walk the
# *entire* channel before it prints anything - slow on channels with thousands of
# videos), this uses "-j" so yt-dlp prints one JSON line per video as it's extracted,
# and stops (killing the process) the moment it reaches a video already in
# existing_ids. So refreshing a 4000-video channel with 5 new uploads only ever scans
# those 5, not the other 3995.
#
# The match is by video ID rather than by full URL string: yt-dlp doesn't always
# return byte-identical URLs for the same video across runs (webpage_url vs. a bare
# ID turned into a URL, stray query params, etc), and comparing full strings meant a
# single non-matching URL could make the "already known" check never fire - forcing
# yt-dlp to walk the *entire* channel every refresh before the code got a chance to
# compare anything. existing_ids should hold video IDs (see _youtube_video_id).
#
# Returns the list of new entry URLs, newest first.
def fetch_channel_new_entries(url, existing_ids, proxy=None, process_holder=None):
    command = [_ytdlp_cmd(), "--no-warnings", "--flat-playlist", "-j"]
    command += ["--proxy", proxy or ""]
    # "--" forces the url to be treated as a positional argument, never as an
    # option - see probe_url's identical comment for why this matters.
    command += ["--", url]
    proc = subprocess.Popen(
        command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        encoding="utf-8", errors="replace", env=_subprocess_env(),
        **_subprocess_no_window_kwargs(),
    )
    if process_holder is not None:
        process_holder(proc)

    # Drain stderr on its own thread so a chatty yt-dlp (warnings, progress, etc.)
    # can't fill the stderr pipe and deadlock us while we're blocked reading stdout.
    stderr_chunks = []

    # Continuously drain the process's stderr on a helper thread so it can never
    # fill its pipe buffer and block the process
    def _drain_stderr():
        try:
            for line in proc.stderr:
                stderr_chunks.append(line)
        except (OSError, ValueError):
            pass

    stderr_thread = threading.Thread(target=_drain_stderr, daemon=True)
    stderr_thread.start()

    # Independent watchdog kills the process if it runs long, since without
    # communicate(timeout=...) there's no built-in way to bound the line-by-line read.
    timed_out = threading.Event()

    # Mark the run as timed out and kill the process so the read loop above unblocks
    def _on_timeout():
        timed_out.set()
        proc.kill()

    watchdog = threading.Timer(PLAYLIST_FETCH_TIMEOUT, _on_timeout)
    watchdog.daemon = True
    watchdog.start()

    entries = []
    stopped_early = False
    try:
        for line in proc.stdout:
            line = line.strip()
            if not line:
                continue
            try:
                entry = json.loads(line)
            except ValueError:
                continue
            if not isinstance(entry, dict):
                continue
            entry_url = _entry_url_from_flat_entry(entry)
            if not entry_url:
                continue
            entry_id = _channel_entry_video_id(entry) or _youtube_video_id(entry_url)
            if entry_id is not None and entry_id in existing_ids:
                stopped_early = True
                proc.kill()
                break
            entries.append(entry_url)
    finally:
        watchdog.cancel()
        proc.stdout.close()
        proc.wait()
        stderr_thread.join(timeout=5)

    if timed_out.is_set():
        raise subprocess.TimeoutExpired(command, PLAYLIST_FETCH_TIMEOUT)
    # A non-zero exit is only an error if we let yt-dlp run to natural completion;
    # if we killed it ourselves after finding the known video, that's expected.
    if proc.returncode != 0 and not stopped_early:
        message = "".join(stderr_chunks).strip().splitlines()
        raise RuntimeError(message[-1] if message else "channel listing failed")
    return {"entries": entries}


# Cross-thread signal carrier for a single playlist-expand task's result/error
class PlaylistSignals(QObject):
    finished = Signal(object, dict)
    error = Signal(object, str)


# Runs one yt-dlp playlist listing on a worker thread and reports back via PlaylistSignals
class PlaylistExpandTask(CancellableTaskMixin, QRunnable):
    # Stash everything fetch_playlist needs, plus cancellation/process-tracking state
    def __init__(self, item, url, proxy=None):
        super().__init__()
        self.item = item
        self.url = url
        self.proxy = proxy
        self.signals = PlaylistSignals()
        self._init_cancellation()

    # Off the GUI thread: fetch the playlist listing and report back (or report an error)
    def run(self):
        if self._cancelled.is_set():
            return
        try:
            info = fetch_playlist(
                self.url, self.proxy, process_holder=self._hold_process
            )
        except FileNotFoundError:
            if not self._cancelled.is_set():
                _safe_emit(self.signals.error, self.item, "yt-dlp not found on PATH")
        except subprocess.TimeoutExpired:
            if not self._cancelled.is_set():
                _safe_emit(self.signals.error, self.item, "playlist fetch timed out")
        except (RuntimeError, ValueError, json.JSONDecodeError) as exc:
            if not self._cancelled.is_set():
                _safe_emit(self.signals.error, self.item, str(exc))
        else:
            if not self._cancelled.is_set():
                _safe_emit(self.signals.finished, self.item, info)


# Cross-thread signal carrier for a channel-refresh task's result/error. Unlike
# PlaylistSignals, this isn't tied to any one tree item - a channel refresh is a
# profile-level action, not something attached to a single link/folder row.
class ChannelRefreshSignals(QObject):
    finished = Signal(dict)
    error = Signal(str)


# Runs "yt-dlp --flat-playlist -j <channel videos url>" on a worker thread (via
# fetch_channel_new_entries) to list a channel's videos for the "Refresh" button,
# stopping as soon as it reaches a video already known, reporting back via
# ChannelRefreshSignals
class ChannelRefreshTask(CancellableTaskMixin, QRunnable):
    # Stash everything fetch_channel_new_entries needs, plus cancellation/process-tracking state
    def __init__(self, url, existing_urls, proxy=None):
        super().__init__()
        self.url = url
        self.existing_urls = existing_urls
        self.proxy = proxy
        self.signals = ChannelRefreshSignals()
        self._init_cancellation()

    # Off the GUI thread: fetch newly-uploaded channel entries and report back
    # (or report an error)
    def run(self):
        if self._cancelled.is_set():
            return
        try:
            info = fetch_channel_new_entries(
                self.url, self.existing_urls, self.proxy, process_holder=self._hold_process
            )
        except FileNotFoundError:
            if not self._cancelled.is_set():
                _safe_emit(self.signals.error, "yt-dlp not found on PATH")
        except subprocess.TimeoutExpired:
            if not self._cancelled.is_set():
                _safe_emit(self.signals.error, "channel refresh timed out")
        except (RuntimeError, ValueError, json.JSONDecodeError) as exc:
            if not self._cancelled.is_set():
                _safe_emit(self.signals.error, str(exc))
        else:
            if not self._cancelled.is_set():
                _safe_emit(self.signals.finished, info)


# Shared behavior for input widgets that should ignore mouse-wheel scrolling, so
# scrolling the page past them doesn't accidentally change their value.
class NoScrollMixin:
    def wheelEvent(self, event):
        event.ignore()


# Combo box that ignores mouse wheel events so scrolling the page doesn't change its value
class NoScrollComboBox(NoScrollMixin, QComboBox):
    pass


# QTreeWidget with drag-and-drop reordering enabled. Whether a given row accepts an
# "on item" drop (nesting something inside it) is controlled per-item via
# Qt.ItemIsDropEnabled (see MainWindow._apply_item_flags) - link rows don't get that
# flag, so Qt itself resolves a drop hovered over a link into an above/below sibling
# reorder instead of nesting under it. After Qt performs the actual move, drop_callback
# (set by the owner) is invoked to renumber/re-save the tree and refresh the UI. It's
# called with a list of (item, old_parent) pairs captured just before the move, so the
# owner can tell which items actually changed folder and relocate their files on disk.
# Folders can only ever sit at the top level - a drop that would nest one folder inside
# another (i.e. drop indicator lands "on" a folder while a folder is being dragged) is
# rejected outright, so folder nesting never goes more than one level deep.
class DraggableTreeWidget(QTreeWidget):
    # No drop/move callback registered until the owner sets one
    def __init__(self, parent=None):
        super().__init__(parent)
        self.drop_callback = None
        self.move_callback = None  # called with "up" or "down" when +/- is pressed

    # "+" moves the current selection up a spot among its siblings, "-" moves it
    # down - same effect as the right-click "Move up"/"Move down" actions, just
    # without opening the context menu first
    def keyPressEvent(self, event):
        no_extra_modifiers = not (event.modifiers() & ~Qt.KeyboardModifier.ShiftModifier)
        if self.move_callback is not None and no_extra_modifiers:
            if event.key() in (Qt.Key.Key_Plus, Qt.Key.Key_Equal):
                self.move_callback("up")
                event.accept()
                return
            if event.key() == Qt.Key.Key_Minus:
                self.move_callback("down")
                event.accept()
                return
        super().keyPressEvent(event)

    # Block dropping a folder onto another folder (no nested folders), then notify
    # the registered drop callback with each moved item's old parent
    def dropEvent(self, event):
        dragged = self.selectedItems()
        target = self.itemAt(event.position().toPoint())
        dragging_folder = any(it.data(0, IS_FOLDER_ROLE) for it in dragged)
        if dragging_folder and target is not None and target.data(0, IS_FOLDER_ROLE) \
                and self.dropIndicatorPosition() == QAbstractItemView.OnItem:
            event.ignore()
            return
        moved = [(item, item.parent()) for item in dragged]
        super().dropEvent(event)
        if self.drop_callback is not None:
            self.drop_callback(moved)


# Spin box that ignores mouse wheel events so scrolling the page doesn't change its value
class NoScrollSpinBox(NoScrollMixin, QSpinBox):
    pass


# Time edit that ignores mouse wheel events so scrolling the page doesn't change its value
class NoScrollTimeEdit(NoScrollMixin, QTimeEdit):
    pass


# Line edit that emits a signal when it loses focus, used for the settings search box
class SettingsSearchLineEdit(QLineEdit):
    focusLost = Signal()

    # Notify listeners once this field loses focus (used to close the settings
    # search dropdown, etc.)
    def focusOutEvent(self, event):
        super().focusOutEvent(event)
        self.focusLost.emit()


# Top-level application window: builds the UI and wires up all placeholder behavior
class MainWindow(QMainWindow):

    # Set up window state, build the UI, and load any saved settings
    def __init__(self):
        super().__init__()
        self.setWindowTitle(APP_NAME)
        self.resize(1000, 600)
        self.setMinimumSize(1000, 600)

        self._log_header = f"{APP_NAME} v{APP_VERSION} — UI ready"
        self._prev_url_text = ""
        self._form_labels = []
        self._donate_row_widgets = []
        self._log_maximized = False
        self._url_placeholder = "Paste url(s) here ..."
        self._settings_search_index = []
        self._settings_search_highlight = None
        self._settings_search_highlight_original = None
        self._log_line_cursors = {}
        # Maps id(item) -> the log block number holding that item's live
        # "|__ NN% of SIZE at SPEED ETA T" progress line, so each update overwrites
        # that same line instead of spamming a new one per percent tick.
        self._download_line_blocks = {}
        # Maps id(item) -> the log block number holding that item's own
        # "Downloading: <name>" line, so it can be rewritten to "Completed: <name>"
        # in place once the download finishes, instead of leaving that line as-is
        # and logging a whole separate "Downloaded: ..." line underneath it.
        self._download_start_blocks = {}
        self._active_probe_count = 0
        self._active_refresh_count = 0
        # Maps id(item) -> the ProbeTask/PlaylistExpandTask currently running for that
        # item, so a removed link/folder can have its in-flight probing stopped.
        self._tasks_by_item = {}
        # The ChannelRefreshTask currently running for the active profile's "Refresh"
        # button, or None if no refresh is in flight
        self._channel_refresh_task = None
        # For a Sub Group profile's "Refresh": the channels ({"name","url"} dicts)
        # still waiting to be refreshed, the one currently in flight (or None), and a
        # running total of new videos added across the whole queue, for the final
        # summary log line - see _start_next_subgroup_channel_refresh.
        self._subgroup_refresh_queue = []
        self._subgroup_refresh_active_channel = None
        self._subgroup_refresh_added_total = 0
        # For a Playlist profile's "Refresh": the playlist folders (top-level items
        # with a PLAYLIST_SOURCE_URL_ROLE) still waiting to be refreshed, and a
        # running total of new videos added across the whole queue, for the final
        # summary log line - see _start_next_playlist_refresh. Unlike the Sub Group
        # queue above, no separate "active" folder needs tracking here since
        # PlaylistExpandTask's own signals already carry the folder item.
        self._playlist_refresh_queue = []
        self._playlist_refresh_added_total = 0
        # Maps link uuid -> current download speed in KB/s, for any download in
        # progress; populated by the (future) download worker via set_download_speed()
        self._download_speeds_kbps = {}
        # "Hide skipped" toggle (background context menu): when True, skipped links
        # are hidden from the tree via setHidden() rather than removed, so toggling
        # it back off instantly brings them all back - see _refresh_skip_visibility.
        self._hide_skipped_links = False
        # The yt-dlp update task currently in flight (if any), so clicking "click to
        # update"/"click to retry" a second time can't start another one on top of it
        self._ytdlp_update_task = None
        # Same as _ytdlp_update_task above, but for the ffmpeg update triggered from
        # the About tab's ffmpeg "click to update" link
        self._ffmpeg_update_task = None
        # Whether the log header's " — UI ready" is currently swapped for a clickable
        # " — update available" (see _set_log_header) - tracked so _reset_log can
        # reapply it after the log is cleared
        self._ytdlp_update_available = False

        set_theme_colors("dark")

        self._load_profile_registry()
        self._load_enabled_plugins_from_disk()

        self._build_ui()

        # Pool of worker threads that run yt-dlp probes. Fixed at 1: probing more
        # than one link at a time isn't needed, so this isn't user-configurable.
        self._probe_pool = QThreadPool()
        self._probe_pool.setMaxThreadCount(1)

        # Pool of worker threads that run real yt-dlp downloads; capacity tracks the
        # "Parallel downloads" setting (kept in sync in _on_parallel_downloads_changed).
        # Maps id(item) -> the DownloadTask currently running for that link.
        self._download_pool = QThreadPool()
        self._download_pool.setMaxThreadCount(self.parallel_downloads_spin.value())
        self._download_tasks = {}

        # Maps id(item) -> number of consecutive download failures since the last
        # successful "started downloading" (progress) event or cooldown. Reset to
        # zero (removed) as soon as a retry actually starts transferring bytes.
        self._download_retry_counts = {}
        # Maps id(item) -> {"item": item, "remaining": seconds} for links currently
        # sitting out a retry cooldown after exhausting their download retries.
        self._download_timeouts = {}
        # Tracks the current "download run" (from the first link starting until the
        # queue drains or the run is stopped) for the "====" summary logged at the
        # end - see _note_download_batch_result/_maybe_log_download_batch_summary.
        # _download_batch_active is False whenever no run is in progress; while True,
        # _download_batch_items maps id(item) -> {"item", "success", "message"} for
        # every link touched at least once during the run (a link that fails then
        # later succeeds on retry ends up recorded as a success - only its state at
        # the moment the run ends is reported).
        self._download_batch_active = False
        self._download_batch_items = {}
        # Ticks every second while any link is cooling down, counting it down and
        # refreshing the "[Ns] - " row prefix; started/stopped on demand.
        self._download_timeout_timer = QTimer(self)
        self._download_timeout_timer.setInterval(1000)
        self._download_timeout_timer.timeout.connect(self._on_download_timeout_tick)

        # Scheduler: the two "last triggered" day-keys stop a start/stop time from
        # firing more than once during the minute it matches.
        self._scheduler_last_start_day = None
        self._scheduler_last_stop_day = None
        self._scheduler_timer = QTimer(self)
        self._scheduler_timer.setInterval(1000)
        self._scheduler_timer.timeout.connect(self._on_scheduler_tick)
        self._scheduler_timer.start()

        # Counts seconds (piggybacking on the once-a-second scheduler tick below)
        # since the About tab's app/yt-dlp/ffmpeg version info was last refreshed,
        # so it can be periodically re-checked without a dedicated QTimer. Reset
        # to 0 each time the refresh fires; see _on_scheduler_tick.
        self._version_refresh_tick_counter = 0

        self._connect_signals()
        self._reset_log()
        self._load_settings_from_disk()
        self._load_links_from_disk()
        self._sync_subgroup_folder_qualities()
        self._update_sidebar_info()
        self._update_status_label()
        self._update_profile_label()
        self._update_refresh_button()
        self._update_ignore_title_pattern_visibility()
        self._update_quality_visibility()
        self._update_number_playlist_downloads_visibility()
        self._update_url_line_edit_for_profile()
        self._update_download_button()
        self._update_subgroup_channels_visibility()

        app = QApplication.instance()
        if app is not None:
            apply_scrollbar_style(app)

        self.centralWidget().setFocus()

        self._start_ytdlp_update_check()
        self._start_ffmpeg_update_check()
        self._start_app_update_check()


    # Assemble the main splitter layout (URL/settings panel, sidebar, log, button row)
    def _build_ui(self):
        self.central = QWidget()
        self.central.setStyleSheet(f"background-color: {BG_WINDOW};")
        self.central.setFocusPolicy(Qt.StrongFocus)
        self.setCentralWidget(self.central)
        v = QVBoxLayout(self.central)
        v.setSpacing(0)

        self.upper_splitter = QSplitter(Qt.Horizontal)
        self.upper_splitter.setHandleWidth(4)
        self.upper_splitter.setOpaqueResize(True)
        self.upper_splitter.addWidget(self._build_left_column())
        self.upper_splitter.addWidget(self._build_right_stack())
        self.upper_splitter.setStretchFactor(0, 4)
        self.upper_splitter.setStretchFactor(1, 1)
        self.upper_splitter.setSizes([690, 288])
        self.upper_splitter.setCollapsible(0, False)
        self.upper_splitter.setCollapsible(1, False)
        self.upper_splitter.handle(1).setEnabled(False)
        self.upper_splitter.setStyleSheet(splitter_handle_style())

        self.log = QTextBrowser()
        self.log.setReadOnly(True)
        self.log.setContextMenuPolicy(Qt.CustomContextMenu)
        self.log.customContextMenuRequested.connect(self._on_log_context_menu)
        self.log.setFrameShape(QTextEdit.NoFrame)
        self.log.setStyleSheet(log_style())
        self.log.viewport().setStyleSheet(f"background-color: {BG_LOG};")
        self.log.setOpenLinks(False)
        self.log.anchorClicked.connect(self._on_log_anchor_clicked)

        self.log_container = QWidget()
        self.log_container.setAttribute(Qt.WA_StyledBackground, True)
        self.log_container.setStyleSheet(panel_style())
        log_container_layout = QVBoxLayout(self.log_container)
        log_container_layout.setContentsMargins(2, 2, 2, 2)
        log_container_layout.addWidget(self.log)

        self.main_splitter = QSplitter(Qt.Vertical)
        self.main_splitter.setHandleWidth(4)
        self.main_splitter.setOpaqueResize(True)
        self.main_splitter.addWidget(self.upper_splitter)
        self.main_splitter.addWidget(self.log_container)
        self.main_splitter.setStretchFactor(0, 1)
        self.main_splitter.setStretchFactor(1, 0)
        self.main_splitter.setSizes([422, 122])
        self.main_splitter.setCollapsible(0, False)
        self.main_splitter.setCollapsible(1, False)
        self.main_splitter.setStyleSheet(splitter_handle_style())
        v.addWidget(self.main_splitter, 1)
        self.main_splitter.handle(1).setEnabled(False)

        v.addSpacing(6)
        v.addLayout(self._build_button_row(), 0)

    # Build the left column: URL input bar stacked above the URL list / settings panel
    def _build_left_column(self):
        self.left_column = QWidget()
        layout = QVBoxLayout(self.left_column)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(4)

        layout.addWidget(self._build_url_widget())
        layout.addWidget(self._build_left_panel(), stretch=1)

        return self.left_column

    # Build the panel that switches between the URL list page and the settings page
    def _build_left_panel(self):
        self.left_widget = QWidget()
        self.left_widget.setAttribute(Qt.WA_StyledBackground, True)
        self.left_widget.setStyleSheet(panel_style())
        left_layout = QVBoxLayout(self.left_widget)
        left_layout.setContentsMargins(0, 0, 0, 0)

        self.left_stack = QStackedWidget()
        self.left_stack.setStyleSheet("background: transparent;")
        left_stack_size_policy = self.left_stack.sizePolicy()
        left_stack_size_policy.setVerticalPolicy(QSizePolicy.Ignored)
        self.left_stack.setSizePolicy(left_stack_size_policy)
        left_layout.addWidget(self.left_stack)

        url_list_page = self._build_url_list_page()
        settings_page = self._build_settings_page()
        self.left_stack.addWidget(url_list_page)
        self.left_stack.addWidget(settings_page)

        return self.left_widget

    # Build the page showing the URL/folder tree
    def _build_url_list_page(self):
        page = QWidget()
        page_layout = QVBoxLayout(page)
        page_layout.setContentsMargins(8, 8, 8, 8)

        self.url_list = DraggableTreeWidget()
        self.url_list.setHeaderHidden(True)
        self.url_list.setColumnCount(1)
        self.url_list.setIndentation(14)
        self.url_list.setStyleSheet(url_list_style())
        self.url_list.setItemDelegate(_NoFocusRectDelegate(self.url_list))
        self.url_list.setSelectionMode(QAbstractItemView.ExtendedSelection)
        self.url_list.setContextMenuPolicy(Qt.CustomContextMenu)
        self.url_list.customContextMenuRequested.connect(self._on_url_list_context_menu)
        # Internal drag-and-drop lets links/folders be reordered, or moved in and out
        # of folders, by dragging rows; per-item flags (_apply_item_flags) stop a link
        # from accepting an "on item" drop, so nothing can be dropped onto a link.
        self.url_list.setDragEnabled(True)
        self.url_list.setAcceptDrops(True)
        self.url_list.setDropIndicatorShown(True)
        self.url_list.setDragDropMode(QAbstractItemView.InternalMove)
        self.url_list.setDefaultDropAction(Qt.MoveAction)
        self.url_list.drop_callback = self._on_url_list_dropped
        self.url_list.move_callback = self._on_url_list_move_key
        page_layout.addWidget(self.url_list)

        return page


    # Build the settings page: tab bar, stacked sub-pages, and the settings field registry
    def _build_settings_page(self):
        page = QWidget()
        page_layout = QVBoxLayout(page)
        page_layout.setContentsMargins(0, 0, 0, 10)
        page_layout.setSpacing(0)

        page_layout.addWidget(self._build_settings_tab_bar())
        settings_body_separator, self.settings_body_separator_line = self._build_percent_separator()
        page_layout.addWidget(settings_body_separator)

        self.settings_stack = QStackedWidget()
        page_layout.addWidget(self.settings_stack, stretch=1)

        self.settings_general = self._build_settings_general_page()
        self.settings_connection = self._build_settings_connection_page()
        self.settings_profiles = self._build_settings_profiles_page()
        self.settings_scheduler = self._build_settings_scheduler_page()
        self.settings_plugins = self._build_settings_plugins_page()
        self.settings_about = self._build_settings_about_page()
        self.settings_stack.addWidget(self.settings_general)
        self.settings_stack.addWidget(self.settings_connection)
        self.settings_stack.addWidget(self.settings_profiles)
        self.settings_stack.addWidget(self.settings_scheduler)
        self.settings_stack.addWidget(self.settings_plugins)
        self.settings_stack.addWidget(self.settings_about)

        self.settings_controls = [
            ("quality", self.quality_combo,
             lambda w: w.currentText(), lambda w, v: w.setCurrentText(v)),
            ("location", self.location_edit,
             lambda w: w.text(), lambda w, v: w.setText(v)),
            ("proxy_enabled", self.chk_proxy,
             lambda w: w.isChecked(), lambda w, v: w.setChecked(v)),
            ("proxy_host", self.proxy_host_edit,
             lambda w: w.text(), lambda w, v: w.setText(v)),
            ("proxy_port", self.proxy_port_spin,
             lambda w: w.value(), lambda w, v: w.setValue(v)),
            ("parallel_downloads", self.parallel_downloads_spin,
             lambda w: w.value(), lambda w, v: w.setValue(v)),
            ("probing_timeout", self.probing_timeout_spin,
             lambda w: w.value(), lambda w, v: w.setValue(v)),
            ("retry_count", self.retry_count_spin,
             lambda w: w.value(), lambda w, v: w.setValue(v)),
            ("download_retry_limit", self.download_retry_limit_spin,
             lambda w: w.value(), lambda w, v: w.setValue(v)),
            ("download_retry_cooldown", self.download_retry_cooldown_spin,
             lambda w: w.value(), lambda w, v: w.setValue(v)),
            ("detailed_log", self.chk_detailed_log,
             lambda w: w.isChecked(), lambda w, v: w.setChecked(v)),
            ("number_playlist_downloads", self.chk_number_playlist_downloads,
             lambda w: w.isChecked(), lambda w, v: w.setChecked(v)),
            ("ignore_title_pattern", self.ignore_title_pattern_edit,
             lambda w: w.text(), lambda w, v: w.setText(v)),
            ("scheduler_start_enabled", self.chk_scheduler_start,
             lambda w: w.isChecked(), lambda w, v: w.setChecked(v)),
            ("scheduler_start_time", self.scheduler_start_time_edit,
             lambda w: w.time().toString("HH:mm"),
             lambda w, v: w.setTime(QTime.fromString(v, "HH:mm"))),
            ("scheduler_stop_enabled", self.chk_scheduler_stop,
             lambda w: w.isChecked(), lambda w, v: w.setChecked(v)),
            ("scheduler_stop_time", self.scheduler_stop_time_edit,
             lambda w: w.time().toString("HH:mm"),
             lambda w, v: w.setTime(QTime.fromString(v, "HH:mm"))),
        ]
        self.settings_committed = self._snapshot_settings()
        # Baseline defaults (as built, before any settings.json is loaded), used to
        # reset the UI when switching to a profile that doesn't have one of its own yet
        self._default_settings_snapshot = dict(self.settings_committed)

        return page

    # Build the OK/Apply/Cancel row shown at the bottom of the settings panel,
    # centered, below settings_stack - shared across every tab since it lives
    # outside the stack rather than inside any one tab's own page
    def _build_settings_action_row(self):
        row = QHBoxLayout()
        row.setSpacing(6)

        ok_btn = UnderlineButton("OK", TEXT_SECONDARY, BORDER_FOCUS)
        apply_btn = UnderlineButton("Apply", TEXT_SECONDARY, BORDER_FOCUS)
        cancel_btn = UnderlineButton("Cancel", MEMBERS_ONLY_COLOR, MEMBERS_ONLY_COLOR)
        for btn in (ok_btn, apply_btn, cancel_btn):
            btn.setMinimumWidth(80)
            btn.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Fixed)

        ok_btn.clicked.connect(self._on_settings_ok)
        apply_btn.clicked.connect(self._on_settings_apply)
        cancel_btn.clicked.connect(self._on_settings_cancel)

        row.addStretch(1)
        row.addWidget(ok_btn)
        row.addWidget(apply_btn)
        row.addWidget(cancel_btn)
        row.addStretch(1)

        return row

    # Build the centered General/Connection/Profiles/Scheduler/Plugins/About tab bar
    def _build_settings_tab_bar(self):
        bar = QWidget()
        self.settings_tab_bar = bar
        bar.setAttribute(Qt.WA_StyledBackground, True)
        bar.setStyleSheet(panel_style())
        bar_layout = QHBoxLayout(bar)
        bar_layout.setContentsMargins(10, 10, 10, 10)
        bar_layout.setSpacing(6)

        self.btn_settings_tab_general = UnderlineButton("General", TEXT_SECONDARY, BORDER_FOCUS)
        self.btn_settings_tab_connection = UnderlineButton("Connection", TEXT_SECONDARY, BORDER_FOCUS)
        self.btn_settings_tab_profiles = UnderlineButton("Profiles", TEXT_SECONDARY, BORDER_FOCUS)
        self.btn_settings_tab_scheduler = UnderlineButton("Scheduler", TEXT_SECONDARY, BORDER_FOCUS)
        self.btn_settings_tab_plugins = UnderlineButton("Plugins", TEXT_SECONDARY, BORDER_FOCUS)
        self.btn_settings_tab_about = UnderlineButton("About", TEXT_SECONDARY, BORDER_FOCUS)

        self.settings_tab_group = QButtonGroup(bar)
        self.settings_tab_group.setExclusive(True)
        bar_layout.addStretch(1)
        for index, btn in enumerate((
            self.btn_settings_tab_general,
            self.btn_settings_tab_connection,
            self.btn_settings_tab_profiles,
            self.btn_settings_tab_scheduler,
            self.btn_settings_tab_plugins,
            self.btn_settings_tab_about,
        )):
            btn.setCheckable(True)
            btn.setMinimumWidth(80)
            self.settings_tab_group.addButton(btn, index)
            bar_layout.addWidget(btn)
        bar_layout.addStretch(1)

        self.btn_settings_tab_general.setChecked(True)
        self.settings_tab_group.idClicked.connect(self._on_settings_tab_clicked)

        return bar

    # Build a horizontal rule that spans a percentage of its container's width
    def _build_percent_separator(self, percent=70, margin_top=8, margin_bottom=8):
        wrapper = QWidget()
        wrapper_layout = QHBoxLayout(wrapper)
        wrapper_layout.setContentsMargins(0, margin_top, 0, margin_bottom)
        wrapper_layout.setSpacing(0)

        line = QFrame()
        line.setFrameShape(QFrame.HLine)
        line.setFrameShadow(QFrame.Plain)
        line.setFixedHeight(1)
        line.setStyleSheet(f"background-color: {BORDER_DISABLED}; border: none;")

        side = (100 - percent) // 2
        wrapper_layout.addStretch(side)
        wrapper_layout.addWidget(line, stretch=percent)
        wrapper_layout.addStretch(side)

        return wrapper, line

    # Switch the settings sub-page
    def _on_settings_tab_clicked(self, index):
        if index == 2:
            self._sync_profiles_with_disk()
        self.settings_stack.setCurrentIndex(index)
        if self.left_stack.currentIndex() == 1:
            self.right_stack.setCurrentIndex(1)

    # Build the General settings tab (quality, download location, theme)
    def _build_settings_general_page(self):
        page = QWidget()
        layout = QVBoxLayout(page)
        layout.setContentsMargins(20, 20, 20, 20)
        layout.setSpacing(14)

        form = QFormLayout()
        form.setSpacing(10)
        form.setLabelAlignment(Qt.AlignLeft)

        self.quality_combo = NoScrollComboBox()
        self.quality_combo.addItems([QUALITY_AUDIO_ONLY, *QUALITY_HEIGHTS, QUALITY_BEST])
        self.quality_combo.setCurrentText(QUALITY_BEST)
        self.quality_combo.setStyleSheet(settings_input_style())
        self.quality_label = self._settings_label("Quality", 0)
        form.addRow(self.quality_label, self.quality_combo)
        self._general_form = form

        location_row = QWidget()
        location_layout = QHBoxLayout(location_row)
        location_layout.setContentsMargins(0, 0, 0, 0)
        location_layout.setSpacing(6)

        self.location_edit = QLineEdit()
        self.location_edit.setPlaceholderText("Choose a folder...")
        self.location_edit.setReadOnly(True)
        self.location_edit.setStyleSheet(settings_input_style())
        # Starting value for a profile that's never had a location explicitly
        # set (see _default_download_dir) - the OS's normal Downloads folder,
        # not blank. Anything actually saved to disk for a profile still wins:
        # _load_settings_from_disk() only overwrites keys present in that
        # profile's settings.json, and only runs after this widget already
        # has this default in it.
        self.location_edit.setText(_default_download_dir())
        location_layout.addWidget(self.location_edit, stretch=1)

        self.btn_browse_location = QPushButton("Browse")
        self.btn_browse_location.setStyleSheet(button_style())
        self.btn_browse_location.clicked.connect(self._on_browse_location)
        location_layout.addWidget(self.btn_browse_location)

        form.addRow(self._settings_label("Download location", 0), location_row)

        layout.addLayout(form)

        self.chk_number_playlist_downloads = QCheckBox(
            "Number playlist downloads (as uploader intended)"
        )
        self.chk_number_playlist_downloads.setChecked(True)
        self.chk_number_playlist_downloads.setStyleSheet(checkbox_style())
        self._settings_search_index.append({
            "text": "Number playlist downloads", "tab_index": 0,
            "widget": self.chk_number_playlist_downloads,
        })
        layout.addWidget(self.chk_number_playlist_downloads)

        # A regex matched against each video's title before it's used to build the
        # downloaded filename, for playlist/channel links only - single-video links
        # keep whatever title yt-dlp reports as-is. Anything the regex matches is
        # dropped, so e.g. "\s*\|.*$" turns "name | unwanted promo text" into just
        # "name" before it hits disk as "name.webm". Left blank, nothing changes.
        ignore_pattern_form = QFormLayout()
        ignore_pattern_form.setSpacing(10)
        ignore_pattern_form.setLabelAlignment(Qt.AlignLeft)

        self.ignore_pattern_label = self._settings_label("Ignore pattern in title (playlist/channel)", 0)
        self.ignore_title_pattern_edit = QLineEdit()
        self.ignore_title_pattern_edit.setPlaceholderText(
            '" - promo text" will be removed from "name - promo text"'
        )
        self.ignore_title_pattern_edit.setStyleSheet(settings_input_style())
        ignore_pattern_form.addRow(self.ignore_pattern_label, self.ignore_title_pattern_edit)
        layout.addLayout(ignore_pattern_form)

        general_separator, self.general_separator_line = self._build_percent_separator()
        layout.addWidget(general_separator)

        self.chk_detailed_log = QCheckBox("Enable detailed log")
        self.chk_detailed_log.setStyleSheet(checkbox_style())
        self._settings_search_index.append({"text": "Enable detailed log", "tab_index": 0, "widget": self.chk_detailed_log})
        layout.addWidget(self.chk_detailed_log)

        layout.addStretch()

        return page

    # Wrap `content` in a borderless, transparent-viewport QScrollArea using the
    # standard panel style - shared by the settings tab pages below.
    def _wrap_in_scroll(self, content):
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.NoFrame)
        scroll.setStyleSheet(panel_style())
        scroll.viewport().setStyleSheet("background: transparent; border: none;")
        scroll.setWidget(content)
        return scroll

    # Build the Connection settings tab (proxy and transfer options)
    def _build_settings_connection_page(self):
        content = QWidget()
        layout = QVBoxLayout(content)
        layout.setContentsMargins(20, 20, 20, 20)
        layout.setSpacing(14)

        self.chk_proxy = QCheckBox("Enable proxy")
        self.chk_proxy.setStyleSheet(checkbox_style())
        self.chk_proxy.stateChanged.connect(self._on_proxy_toggled)
        self._settings_search_index.append({"text": "Enable proxy", "tab_index": 1, "widget": self.chk_proxy})
        layout.addWidget(self.chk_proxy)

        form = QFormLayout()
        form.setSpacing(10)
        form.setLabelAlignment(Qt.AlignLeft)

        self.proxy_host_edit = QLineEdit()
        self.proxy_host_edit.setPlaceholderText("127.0.0.1")
        self.proxy_host_edit.setStyleSheet(settings_input_style())
        # Restrict to a valid IPv4 address (four 0-255 octets) - a proxy host here is
        # always a plain 32-bit IP, never a hostname. Each octet pattern rejects
        # anything above 255 (e.g. "256", "999") while still matching as the user
        # types each digit, so QRegularExpressionValidator treats an in-progress
        # entry like "192." as Intermediate rather than snapping straight to Invalid.
        ipv4_octet = r"(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)"
        ipv4_pattern = QRegularExpression(rf"^{ipv4_octet}(\.{ipv4_octet}){{3}}$")
        self.proxy_host_edit.setValidator(QRegularExpressionValidator(ipv4_pattern, self.proxy_host_edit))
        form.addRow(self._settings_label("Proxy host", 1), self.proxy_host_edit)

        self.proxy_port_spin = NoScrollSpinBox()
        self.proxy_port_spin.setRange(1, 65535)
        self.proxy_port_spin.setValue(8080)
        self.proxy_port_spin.setStyleSheet(settings_input_style())
        self.proxy_port_spin.setButtonSymbols(QSpinBox.NoButtons)
        form.addRow(self._settings_label("Proxy port", 1), self.proxy_port_spin)

        self.proxy_host_edit.setEnabled(False)
        self.proxy_port_spin.setEnabled(False)

        layout.addLayout(form)

        connection_separator, self.connection_separator_line = self._build_percent_separator()
        layout.addWidget(connection_separator)

        transfer_form = QFormLayout()
        transfer_form.setSpacing(10)
        transfer_form.setLabelAlignment(Qt.AlignLeft)

        self.parallel_downloads_spin = NoScrollSpinBox()
        self.parallel_downloads_spin.setRange(1, 10)
        self.parallel_downloads_spin.setValue(1)
        self.parallel_downloads_spin.setStyleSheet(settings_input_style())
        self.parallel_downloads_spin.setButtonSymbols(QSpinBox.NoButtons)
        transfer_form.addRow(self._settings_label("Parallel downloads", 1), self.parallel_downloads_spin)

        self.probing_timeout_spin = NoScrollSpinBox()
        self.probing_timeout_spin.setRange(1, 120)
        self.probing_timeout_spin.setValue(10)
        self.probing_timeout_spin.setStyleSheet(settings_input_style())
        self.probing_timeout_spin.setButtonSymbols(QSpinBox.NoButtons)
        transfer_form.addRow(self._settings_label("Probing timeout (s)", 1), self.probing_timeout_spin)

        self.retry_count_spin = NoScrollSpinBox()
        self.retry_count_spin.setRange(0, 20)
        self.retry_count_spin.setValue(3)
        self.retry_count_spin.setStyleSheet(settings_input_style())
        self.retry_count_spin.setButtonSymbols(QSpinBox.NoButtons)
        transfer_form.addRow(self._settings_label("Retry count", 1), self.retry_count_spin)

        self.download_retry_limit_spin = NoScrollSpinBox()
        self.download_retry_limit_spin.setRange(1, 20)
        self.download_retry_limit_spin.setValue(4)
        self.download_retry_limit_spin.setStyleSheet(settings_input_style())
        self.download_retry_limit_spin.setButtonSymbols(QSpinBox.NoButtons)
        transfer_form.addRow(
            self._settings_label("Download failure retries", 1), self.download_retry_limit_spin,
        )

        self.download_retry_cooldown_spin = NoScrollSpinBox()
        self.download_retry_cooldown_spin.setRange(5, 3600)
        self.download_retry_cooldown_spin.setValue(300)
        self.download_retry_cooldown_spin.setStyleSheet(settings_input_style())
        self.download_retry_cooldown_spin.setButtonSymbols(QSpinBox.NoButtons)
        transfer_form.addRow(
            self._settings_label("Retry cooldown (s)", 1), self.download_retry_cooldown_spin,
        )

        layout.addLayout(transfer_form)
        layout.addStretch()

        return self._wrap_in_scroll(content)

    # Minimum pixel height for a QListWidget to always show at least `rows` rows
    # before it starts scrolling internally (via its own built-in scrollbar), no
    # matter how little space the surrounding layout would otherwise squeeze it
    # down to. Row height mirrors profile_list_style()'s "padding: 3px 6px" plus a
    # couple pixels of breathing room. Both settings-page lists use 5 rows.
    def _list_min_height_for_rows(self, list_widget, rows):
        row_height = list_widget.fontMetrics().height() + 8
        return row_height * rows + 2 * list_widget.frameWidth() + 4

    # Grows `list_widget` to a fixed height that fits every one of its current
    # rows (falling back to _list_min_height_for_rows' `min_rows` height when
    # that's taller, e.g. an empty or near-empty list) and turns off its own
    # vertical scrollbar. Used for the Profiles tab's profile_list and
    # subgroup_channel_list so neither ever scrolls internally - instead the
    # list grows to show every row and the settings page's own outer scroll
    # area (see _wrap_in_scroll) is what scrolls when the tab's content is
    # taller than the window. Call this after (re)populating the list.
    def _resize_list_to_contents(self, list_widget, min_rows=5):
        content_height = sum(
            list_widget.sizeHintForRow(i) for i in range(list_widget.count())
        )
        content_height += 2 * list_widget.frameWidth() + 4
        min_height = self._list_min_height_for_rows(list_widget, min_rows)
        list_widget.setFixedHeight(max(min_height, content_height))

    # Build the Profiles settings tab (profile selector and list)
    def _build_settings_profiles_page(self):
        content = QWidget()
        layout = QVBoxLayout(content)
        layout.setContentsMargins(20, 20, 20, 20)
        layout.setSpacing(14)

        form = QFormLayout()
        form.setSpacing(10)
        form.setLabelAlignment(Qt.AlignLeft)

        profile_row = QWidget()
        profile_layout = QHBoxLayout(profile_row)
        profile_layout.setContentsMargins(0, 0, 0, 0)
        profile_layout.setSpacing(6)

        self.profile_combo = NoScrollComboBox()
        self.profile_combo.addItems([p["name"] for p in self._profiles])
        self.profile_combo.setCurrentText(self._current_profile_name)
        self.profile_combo.setStyleSheet(settings_input_style())
        profile_layout.addWidget(self.profile_combo, stretch=1)

        self.btn_new_profile = QPushButton("New...")
        self.btn_new_profile.setStyleSheet(button_style())
        self.btn_new_profile.clicked.connect(self._on_new_profile_clicked)
        profile_layout.addWidget(self.btn_new_profile)

        self.btn_delete_profile = QPushButton("Delete")
        self.btn_delete_profile.setStyleSheet(button_style())
        self.btn_delete_profile.clicked.connect(self._on_delete_profile_clicked)
        profile_layout.addWidget(self.btn_delete_profile)

        form.addRow(self._settings_label("Profile", 2), profile_row)

        layout.addLayout(form)

        layout.addWidget(self._settings_label("Available profiles", 2))

        self.profile_list = QListWidget()
        self.profile_list.setStyleSheet(profile_list_style())
        self.profile_list.setFrameShape(QListWidget.NoFrame)
        self.profile_list.setItemDelegate(_ProfileListSeparatorDelegate(self.profile_list))
        self.profile_list.setContextMenuPolicy(Qt.CustomContextMenu)
        self.profile_list.customContextMenuRequested.connect(self._on_profile_list_context_menu)
        # No internal scrollbar - the list grows to fit every profile and the
        # settings page itself scrolls instead (see _resize_list_to_contents).
        self.profile_list.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.profile_list.setMinimumHeight(self._list_min_height_for_rows(self.profile_list, 5))
        layout.addWidget(self.profile_list)

        # Shown only while the active profile is a "Sub Group" - lets its channels
        # (each with its own tracking folder in the sidebar - see
        # _get_or_create_named_folder) be added to or removed after creation.
        self.subgroup_channels_label = self._settings_label("Channels in this sub group", 2)
        layout.addWidget(self.subgroup_channels_label)

        self.subgroup_channel_list = QListWidget()
        self.subgroup_channel_list.setStyleSheet(profile_list_style())
        self.subgroup_channel_list.setFrameShape(QListWidget.NoFrame)
        # No internal scrollbar - the list grows to fit every channel and the
        # settings page itself scrolls instead (see _resize_list_to_contents).
        self.subgroup_channel_list.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.subgroup_channel_list.setMinimumHeight(
            self._list_min_height_for_rows(self.subgroup_channel_list, 5)
        )
        layout.addWidget(self.subgroup_channel_list)

        self.subgroup_channel_button_row = QWidget()
        subgroup_button_layout = QHBoxLayout(self.subgroup_channel_button_row)
        subgroup_button_layout.setContentsMargins(0, 0, 0, 0)
        subgroup_button_layout.setSpacing(6)

        self.btn_add_channel = QPushButton("Add Channel...")
        self.btn_add_channel.setStyleSheet(button_style())
        self.btn_add_channel.clicked.connect(self._on_add_channel_clicked)
        subgroup_button_layout.addWidget(self.btn_add_channel)

        self.btn_remove_channel = QPushButton("Remove Channel")
        self.btn_remove_channel.setStyleSheet(button_style())
        self.btn_remove_channel.clicked.connect(self._on_remove_channel_clicked)
        subgroup_button_layout.addWidget(self.btn_remove_channel)
        subgroup_button_layout.addStretch()
        layout.addWidget(self.subgroup_channel_button_row)

        # Sub Group-only: number every download by its real upload time (oldest
        # first) across ALL of the group's channels combined, and download in that
        # same order - instead of the usual "number within its own channel folder,
        # download top-to-bottom in the tree" behavior. See
        # _subgroup_upload_order_map for how this is computed.
        self.chk_subgroup_number_by_upload_order = QCheckBox(
            "Number downloads by order, oldest first"
        )
        self.chk_subgroup_number_by_upload_order.setToolTip(
            "Number every download by its real upload time, oldest first, across all "
            "channels in this sub group combined - instead of numbering within each "
            "channel's own folder in tree order."
        )
        self.chk_subgroup_number_by_upload_order.setStyleSheet(checkbox_style())
        self.chk_subgroup_number_by_upload_order.toggled.connect(
            self._on_subgroup_number_by_upload_order_toggled
        )
        layout.addWidget(self.chk_subgroup_number_by_upload_order)

        # Collects any leftover vertical space (e.g. when the sub-group-only
        # widgets above are hidden and the remaining content is shorter than
        # the scroll area's viewport) at the bottom of the page instead of it
        # being spread out between widgets by the layout.
        layout.addStretch()

        self._reload_profile_list()

        return self._wrap_in_scroll(content)

    # Build the Scheduler settings tab: automatic start/stop times and an optional
    # data-transfer cap measured from an automatic start
    def _build_settings_scheduler_page(self):
        page = QWidget()
        layout = QVBoxLayout(page)
        layout.setContentsMargins(20, 20, 20, 20)
        layout.setSpacing(10)

        self.chk_scheduler_start = QCheckBox("Automatically start downloads at")
        self.chk_scheduler_start.setStyleSheet(checkbox_style())
        self.chk_scheduler_start.stateChanged.connect(self._on_scheduler_start_toggled)
        self._settings_search_index.append({
            "text": "Automatically start downloads at", "tab_index": 3,
            "widget": self.chk_scheduler_start,
        })
        layout.addWidget(self.chk_scheduler_start)

        start_form = QFormLayout()
        start_form.setSpacing(10)
        start_form.setLabelAlignment(Qt.AlignLeft)
        self.scheduler_start_time_edit = NoScrollTimeEdit()
        self.scheduler_start_time_edit.setDisplayFormat("HH:mm")
        self.scheduler_start_time_edit.setTime(QTime(9, 0))
        self.scheduler_start_time_edit.setStyleSheet(settings_input_style())
        self.scheduler_start_time_edit.setButtonSymbols(QSpinBox.NoButtons)
        self.scheduler_start_time_edit.setEnabled(False)
        start_form.addRow(self._settings_label("Start time", 3), self.scheduler_start_time_edit)
        layout.addLayout(start_form)

        layout.addSpacing(4)

        self.chk_scheduler_stop = QCheckBox("Automatically stop downloads at")
        self.chk_scheduler_stop.setStyleSheet(checkbox_style())
        self.chk_scheduler_stop.stateChanged.connect(self._on_scheduler_stop_toggled)
        self._settings_search_index.append({
            "text": "Automatically stop downloads at", "tab_index": 3,
            "widget": self.chk_scheduler_stop,
        })
        layout.addWidget(self.chk_scheduler_stop)

        stop_form = QFormLayout()
        stop_form.setSpacing(10)
        stop_form.setLabelAlignment(Qt.AlignLeft)
        self.scheduler_stop_time_edit = NoScrollTimeEdit()
        self.scheduler_stop_time_edit.setDisplayFormat("HH:mm")
        self.scheduler_stop_time_edit.setTime(QTime(18, 0))
        self.scheduler_stop_time_edit.setStyleSheet(settings_input_style())
        self.scheduler_stop_time_edit.setButtonSymbols(QSpinBox.NoButtons)
        self.scheduler_stop_time_edit.setEnabled(False)
        stop_form.addRow(self._settings_label("Stop time", 3), self.scheduler_stop_time_edit)
        layout.addLayout(stop_form)

        layout.addStretch()
        return page

    # Build the Plugins settings tab: a Browse... button (restricted to the
    # plugins/ folder next to the executable/script, and to files starting with
    # the PLUGIN_MARKER_COMMENT) with the list of currently-added plugins below it
    def _build_settings_plugins_page(self):
        page = QWidget()
        layout = QVBoxLayout(page)
        layout.setContentsMargins(20, 20, 20, 20)
        layout.setSpacing(10)

        self.plugins_note_label = QLabel("Placeholder feature, no current functionality")
        self.plugins_note_label.setWordWrap(True)
        self.plugins_note_label.setStyleSheet(sidebar_label_muted_style())
        layout.addWidget(self.plugins_note_label)

        browse_row = QWidget()
        browse_layout = QHBoxLayout(browse_row)
        browse_layout.setContentsMargins(0, 0, 0, 0)
        browse_layout.setSpacing(6)

        self.btn_browse_plugin = QPushButton("Browse...")
        self.btn_browse_plugin.setStyleSheet(button_style())
        self.btn_browse_plugin.clicked.connect(self._on_browse_plugin_clicked)
        browse_layout.addWidget(self.btn_browse_plugin)
        browse_layout.addStretch()

        self._settings_search_index.append({
            "text": "Browse...", "tab_index": 4, "widget": self.btn_browse_plugin,
        })
        layout.addWidget(browse_row)

        self.plugin_list = QListWidget()
        self.plugin_list.setStyleSheet(profile_list_style())
        self.plugin_list.setFrameShape(QListWidget.NoFrame)
        self.plugin_list.setContextMenuPolicy(Qt.CustomContextMenu)
        self.plugin_list.customContextMenuRequested.connect(self._on_plugin_list_context_menu)
        layout.addWidget(self.plugin_list, stretch=1)

        self._reload_plugin_list()

        return page

    # Build the About settings tab
    def _build_settings_about_page(self):
        content = QWidget()
        layout = QVBoxLayout(content)
        layout.setContentsMargins(20, 20, 20, 20)
        layout.setSpacing(6)

        self.about_name_label = QLabel(APP_NAME)
        self.about_name_label.setStyleSheet(
            f"color: {TEXT_PRIMARY}; font-size: 16px; font-weight: bold;"
        )
        layout.addWidget(self.about_name_label)

        self.about_description_label = QLabel(
            "A download manager for censored or unstable connections with "
            "features to allow channel tracking or playlist downloads."
        )
        self.about_description_label.setWordWrap(True)
        self.about_description_label.setStyleSheet(sidebar_label_muted_style())
        layout.addWidget(self.about_description_label)

        about_donate_separator, _ = self._build_percent_separator(
            margin_top=12, margin_bottom=12
        )
        layout.addWidget(about_donate_separator)

        self.about_donate_label = QLabel(
            "ytdlp-links is provided absolutely free of charge with source code "
            "available under GPLv3 licence on github. If this program has been "
            "useful to you in any way consider donating using one of the methods "
            "below:"
        )
        self.about_donate_label.setWordWrap(True)
        self.about_donate_label.setStyleSheet(sidebar_label_muted_style())
        layout.addWidget(self.about_donate_label)

        self.about_donate_toggle_label = QLabel(
            f'<a href="toggle" style="color: {BORDER_FOCUS}; text-decoration: none;">&#9656; expand</a>'
        )
        self.about_donate_toggle_label.setStyleSheet(sidebar_label_muted_style())
        self.about_donate_toggle_label.setTextFormat(Qt.RichText)
        self.about_donate_toggle_label.setTextInteractionFlags(Qt.LinksAccessibleByMouse)
        self.about_donate_toggle_label.setCursor(Qt.PointingHandCursor)
        self.about_donate_toggle_label.linkActivated.connect(self._on_about_donate_toggle_clicked)
        layout.addWidget(self.about_donate_toggle_label)

        # Collapsible 3-row donation methods list, hidden until the toggle above is
        # clicked (see _on_about_donate_toggle_clicked)
        self.about_donate_rows_widget = QWidget()
        about_donate_rows_layout = QVBoxLayout(self.about_donate_rows_widget)
        about_donate_rows_layout.setContentsMargins(0, 4, 0, 0)
        about_donate_rows_layout.setSpacing(4)
        # All title labels ("ETH:", "USDT (ERC20):", ...) share one fixed width -
        # the widest one needs - so every row's value field lines up regardless
        # of how long that row's title text is.
        donate_title_width = max(
            QFontMetrics(self.font()).horizontalAdvance(f"{title}:")
            for title, _ in self._DONATE_METHODS
        )
        for title, value in self._DONATE_METHODS:
            about_donate_rows_layout.addWidget(
                self._build_donate_row(title, value, donate_title_width)
            )
        self.about_donate_rows_widget.setVisible(False)
        layout.addWidget(self.about_donate_rows_widget)

        about_separator, self.about_separator_line = self._build_percent_separator(
            margin_top=12, margin_bottom=12
        )
        layout.addWidget(about_separator)

        self.about_version_label = QLabel(f"app version: {APP_VERSION}")
        self.about_version_label.setStyleSheet(sidebar_label_muted_style())
        layout.addWidget(self.about_version_label)

        # Tree-style status line under "app version: ..." - same pattern as the
        # yt-dlp/ffmpeg ones below (see _start_app_update_check), except with no
        # "click to update" link, since there's no in-place update mechanism for
        # the app itself yet (see get_latest_app_version/APP_LATEST_RELEASE_URL).
        app_update_row = QWidget()
        app_update_row_layout = QHBoxLayout(app_update_row)
        app_update_row_layout.setContentsMargins(0, 0, 0, 0)
        app_update_row_layout.setSpacing(10)

        self.about_app_update_text_label = QLabel("")
        self.about_app_update_text_label.setStyleSheet(sidebar_label_muted_style())
        app_update_row_layout.addWidget(self.about_app_update_text_label)
        app_update_row_layout.addStretch(1)

        self.about_app_update_link_label = QLabel("")
        self.about_app_update_link_label.setStyleSheet(
            f"color: {BORDER_FOCUS}; font-size: 11px; text-decoration: underline;"
        )
        self.about_app_update_link_label.setTextInteractionFlags(Qt.LinksAccessibleByMouse)
        self.about_app_update_link_label.setCursor(Qt.PointingHandCursor)
        self.about_app_update_link_label.linkActivated.connect(self._on_app_update_link_clicked)
        app_update_row_layout.addWidget(self.about_app_update_link_label)

        layout.addWidget(app_update_row)

        layout.addSpacing(10)  # extra breathing room before the yt-dlp version line

        ytdlp_version = get_ytdlp_version()
        self.about_ytdlp_version_label = QLabel(
            f"yt-dlp version: {ytdlp_version}" if ytdlp_version else "yt-dlp version: not found"
        )
        self.about_ytdlp_version_label.setStyleSheet(sidebar_label_muted_style())
        layout.addWidget(self.about_ytdlp_version_label)

        # Tree-style status line under "yt-dlp version: ..." (empty/hidden until the
        # automatic check in _start_ytdlp_update_check reports something), e.g.:
        #   └── new version available                          click to update
        ytdlp_update_row = QWidget()
        ytdlp_update_row_layout = QHBoxLayout(ytdlp_update_row)
        ytdlp_update_row_layout.setContentsMargins(0, 0, 0, 0)
        ytdlp_update_row_layout.setSpacing(10)

        self.about_ytdlp_update_text_label = QLabel("")
        self.about_ytdlp_update_text_label.setStyleSheet(sidebar_label_muted_style())
        ytdlp_update_row_layout.addWidget(self.about_ytdlp_update_text_label)
        ytdlp_update_row_layout.addStretch(1)

        self.about_ytdlp_update_link_label = QLabel("")
        self.about_ytdlp_update_link_label.setStyleSheet(
            f"color: {BORDER_FOCUS}; font-size: 11px; text-decoration: underline;"
        )
        self.about_ytdlp_update_link_label.setTextInteractionFlags(Qt.LinksAccessibleByMouse)
        self.about_ytdlp_update_link_label.setCursor(Qt.PointingHandCursor)
        self.about_ytdlp_update_link_label.linkActivated.connect(self._on_ytdlp_update_link_clicked)
        ytdlp_update_row_layout.addWidget(self.about_ytdlp_update_link_label)

        layout.addWidget(ytdlp_update_row)

        layout.addSpacing(10)  # extra breathing room before the ffmpeg version line, same as above

        ffmpeg_version = get_ffmpeg_version()
        self.about_ffmpeg_version_label = QLabel(
            f"ffmpeg version: {_ffmpeg_version_display(ffmpeg_version)}" if ffmpeg_version else "ffmpeg version: not found"
        )
        self.about_ffmpeg_version_label.setStyleSheet(sidebar_label_muted_style())
        layout.addWidget(self.about_ffmpeg_version_label)

        # Tree-style status line under "ffmpeg version: ...", same pattern as the
        # yt-dlp one above (see _start_ffmpeg_update_check)
        ffmpeg_update_row = QWidget()
        ffmpeg_update_row_layout = QHBoxLayout(ffmpeg_update_row)
        ffmpeg_update_row_layout.setContentsMargins(0, 0, 0, 0)
        ffmpeg_update_row_layout.setSpacing(10)

        self.about_ffmpeg_update_text_label = QLabel("")
        self.about_ffmpeg_update_text_label.setStyleSheet(sidebar_label_muted_style())
        ffmpeg_update_row_layout.addWidget(self.about_ffmpeg_update_text_label)
        ffmpeg_update_row_layout.addStretch(1)

        self.about_ffmpeg_update_link_label = QLabel("")
        self.about_ffmpeg_update_link_label.setStyleSheet(
            f"color: {BORDER_FOCUS}; font-size: 11px; text-decoration: underline;"
        )
        self.about_ffmpeg_update_link_label.setTextInteractionFlags(Qt.LinksAccessibleByMouse)
        self.about_ffmpeg_update_link_label.setCursor(Qt.PointingHandCursor)
        self.about_ffmpeg_update_link_label.linkActivated.connect(self._on_ffmpeg_update_link_clicked)
        ffmpeg_update_row_layout.addWidget(self.about_ffmpeg_update_link_label)

        layout.addWidget(ffmpeg_update_row)

        layout.addStretch()

        return self._wrap_in_scroll(content)

    # Expands/collapses the 3-row donation methods list under the About tab's donate
    # blurb, flipping the toggle link's arrow/wording to match
    def _on_about_donate_toggle_clicked(self, href):
        expanded = not self.about_donate_rows_widget.isVisible()
        self.about_donate_rows_widget.setVisible(expanded)
        verb = "collapse" if expanded else "expand"
        arrow = "&#9662;" if expanded else "&#9656;"  # ▾ expanded, ▸ collapsed
        self.about_donate_toggle_label.setText(
            f'<a href="toggle" style="color: {BORDER_FOCUS}; text-decoration: none;">{arrow} {verb}</a>'
        )

    # Build one row of the donate section: a title label (e.g. "Bitcoin") next to
    # a read-only, click-to-select field holding the actual address/handle, plus
    # a "Copy" button for grabbing it in one click. Value/copy widgets are kept
    # in self._donate_row_widgets so _refresh_theme_styles can restyle them.
    def _build_donate_row(self, title, value, title_width):
        row = QWidget()
        row_layout = QHBoxLayout(row)
        row_layout.setContentsMargins(0, 0, 0, 0)
        row_layout.setSpacing(8)

        title_label = QLabel(f"{title}:")
        title_label.setStyleSheet(sidebar_label_muted_style())
        title_label.setFixedWidth(title_width)
        row_layout.addWidget(title_label)

        value_edit = QLineEdit(value)
        value_edit.setReadOnly(True)
        value_edit.setCursorPosition(0)
        value_edit.setStyleSheet(settings_input_style())
        row_layout.addWidget(value_edit, 1)

        copy_btn = QPushButton("Copy")
        copy_btn.setFixedWidth(50)
        copy_btn.setStyleSheet(button_style())
        copy_btn.clicked.connect(lambda: self._copy_to_clipboard(value, copy_btn))
        row_layout.addWidget(copy_btn)

        self._donate_row_widgets.append((value_edit, copy_btn))
        return row

    # Copy text to the clipboard, briefly flashing the triggering button's label
    # to "Copied!" as feedback before reverting it.
    def _copy_to_clipboard(self, text, feedback_btn=None):
        QGuiApplication.clipboard().setText(text)
        if feedback_btn is not None:
            original = feedback_btn.text()
            feedback_btn.setText("Copied!")
            # Disabling a focused widget makes Qt auto-advance focus to the next
            # widget in the tab chain (the row below's value field), which shows
            # up as that row getting highlighted. Drop focus first so nothing
            # visibly steals it.
            feedback_btn.clearFocus()
            feedback_btn.setEnabled(False)
            QTimer.singleShot(1200, lambda: (feedback_btn.setText(original), feedback_btn.setEnabled(True)))

    # Kick off a background check of yt-dlp's latest released version and compare it
    # against what's installed, showing the result as a tree-style line under the
    # version label. Runs automatically once at app startup (see __init__) and again
    # any time "click to retry" is used. Everything, including looking up the
    # installed version, happens on a worker thread (see YtdlpUpdateCheckTask) so
    # this never blocks the UI.
    def _start_ytdlp_update_check(self):
        self.about_ytdlp_update_text_label.setText("└── checking for updates…")
        self.about_ytdlp_update_link_label.setText("")
        self.settings_update_label.setText("update: checking…")
        task = YtdlpUpdateCheckTask(proxy=self._current_proxy())
        task.signals.finished.connect(self._on_ytdlp_update_check_finished)
        QThreadPool.globalInstance().start(task)

    # Reports the result of _start_ytdlp_update_check back on the GUI thread
    def _on_ytdlp_update_check_finished(self, installed_version, latest_version):
        self.about_ytdlp_version_label.setText(
            f"yt-dlp version: {installed_version}" if installed_version else "yt-dlp version: not found"
        )
        if not installed_version:
            self.about_ytdlp_update_text_label.setText("└── not installed")
            self.about_ytdlp_update_link_label.setText(
                f'<a href="update" style="color: {BORDER_FOCUS}; text-decoration: underline;">click to download</a>'
            )
            self.settings_update_label.setText("update: yt-dlp not found")
            self._set_log_header("UI ready", clickable=False)
        elif not latest_version:
            self.about_ytdlp_update_text_label.setText("└── could not check for updates")
            self.about_ytdlp_update_link_label.setText(
                f'<a href="check" style="color: {BORDER_FOCUS}; text-decoration: underline;">click to retry</a>'
            )
            self.settings_update_label.setText("update: could not check")
            self._set_log_header("UI ready", clickable=False)
        elif installed_version == latest_version:
            self.about_ytdlp_update_text_label.setText("└── up to date")
            self.about_ytdlp_update_link_label.setText("")
            self.settings_update_label.setText("update: up to date")
            self._set_log_header("UI ready", clickable=False)
        else:
            self.about_ytdlp_update_text_label.setText(f"└── new version available: {latest_version}")
            self.about_ytdlp_update_link_label.setText(
                f'<a href="update" style="color: {BORDER_FOCUS}; text-decoration: underline;">click to update</a>'
            )
            self.settings_update_label.setText(f"update: {latest_version} available")
            self._set_log_header("update available", clickable=True)

    # Handles both links that can appear next to the tree-style status line: retrying
    # a failed update check, and actually running the update
    def _on_ytdlp_update_link_clicked(self, href):
        if href == "check":
            self._start_ytdlp_update_check()
        elif href == "update":
            self._start_ytdlp_update()

    # Runs "yt-dlp -U" in the background and reports the result once it's done.
    # Guards against double-clicks via _ytdlp_update_task, since the link stays
    # clickable while the update is running.
    def _start_ytdlp_update(self):
        if self._ytdlp_update_task is not None:
            return
        self.about_ytdlp_update_text_label.setText("└── updating…")
        self.about_ytdlp_update_link_label.setText("")
        self.settings_update_label.setText("update: updating…")
        self._log("Starting yt-dlp update…")
        task = YtdlpUpdateTask(proxy=self._current_proxy())
        task.signals.step.connect(self._on_ytdlp_update_step)
        task.signals.finished.connect(self._on_ytdlp_update_finished)
        self._ytdlp_update_task = task
        QThreadPool.globalInstance().start(task)

    # Logs one line of update progress as it happens (see update_ytdlp's log callback)
    def _on_ytdlp_update_step(self, message):
        self._log(message)

    # Reports the result of _start_ytdlp_update back on the GUI thread: refreshes the
    # displayed yt-dlp version and updates the tree-style status line. The step-by-step
    # output was already logged live via _on_ytdlp_update_step, so only a final
    # succeeded/failed summary line is added here.
    def _on_ytdlp_update_finished(self, success, output, new_version):
        self._ytdlp_update_task = None
        self.about_ytdlp_version_label.setText(
            f"yt-dlp version: {new_version}" if new_version else "yt-dlp version: not found"
        )
        self._log(f"yt-dlp update {'succeeded' if success else 'failed'}")
        if success:
            self.about_ytdlp_update_text_label.setText("└── up to date")
            self.about_ytdlp_update_link_label.setText("")
            self.settings_update_label.setText("update: up to date")
            self._set_log_header("UI ready", clickable=False)
        else:
            self.about_ytdlp_update_text_label.setText("└── update failed - see log")
            self.about_ytdlp_update_link_label.setText(
                f'<a href="update" style="color: {BORDER_FOCUS}; text-decoration: underline;">click to retry</a>'
            )
            self.settings_update_label.setText("update: update failed")

    # Same as _start_ytdlp_update_check, but for this app's bundled ffmpeg - see
    # FfmpegUpdateCheckTask. Runs automatically once at app startup (see __init__)
    # and again any time "click to retry" is used.
    def _start_ffmpeg_update_check(self):
        self.about_ffmpeg_update_text_label.setText("└── checking for updates…")
        self.about_ffmpeg_update_link_label.setText("")
        task = FfmpegUpdateCheckTask(proxy=self._current_proxy())
        task.signals.finished.connect(self._on_ffmpeg_update_check_finished)
        QThreadPool.globalInstance().start(task)

    # Reports the result of _start_ffmpeg_update_check back on the GUI thread.
    # Comparison is by build date (see _ffmpeg_version_build_date) rather than
    # exact string equality, since yt-dlp/FFmpeg-Builds' "latest" release is a
    # floating build with no version number of its own to compare against - see
    # get_latest_ffmpeg_version.
    def _on_ffmpeg_update_check_finished(self, installed_version, latest_date):
        self.about_ffmpeg_version_label.setText(
            f"ffmpeg version: {_ffmpeg_version_display(installed_version)}" if installed_version else "ffmpeg version: not found"
        )
        if not installed_version:
            self.about_ffmpeg_update_text_label.setText("└── not installed")
            self.about_ffmpeg_update_link_label.setText(
                f'<a href="update" style="color: {BORDER_FOCUS}; text-decoration: underline;">click to download</a>'
            )
            return
        installed_date = _ffmpeg_version_build_date(installed_version)
        if not latest_date:
            self.about_ffmpeg_update_text_label.setText("└── could not check for updates")
            self.about_ffmpeg_update_link_label.setText(
                f'<a href="check" style="color: {BORDER_FOCUS}; text-decoration: underline;">click to retry</a>'
            )
        elif installed_date and installed_date >= latest_date:
            self.about_ffmpeg_update_text_label.setText("└── up to date")
            self.about_ffmpeg_update_link_label.setText("")
        else:
            latest_display = f"{latest_date[0:4]}.{latest_date[4:6]}.{latest_date[6:8]}"
            self.about_ffmpeg_update_text_label.setText(f"└── new version available: {latest_display}")
            self.about_ffmpeg_update_link_label.setText(
                f'<a href="update" style="color: {BORDER_FOCUS}; text-decoration: underline;">click to update</a>'
            )

    # Handles both links that can appear next to the ffmpeg tree-style status line,
    # same as _on_ytdlp_update_link_clicked
    def _on_ffmpeg_update_link_clicked(self, href):
        if href == "check":
            self._start_ffmpeg_update_check()
        elif href == "update":
            self._start_ffmpeg_update()

    # Downloads and installs the latest ffmpeg build in the background and reports
    # the result once it's done. Guards against double-clicks via
    # _ffmpeg_update_task, same as _start_ytdlp_update.
    def _start_ffmpeg_update(self):
        if self._ffmpeg_update_task is not None:
            return
        self.about_ffmpeg_update_text_label.setText("└── updating…")
        self.about_ffmpeg_update_link_label.setText("")
        self._log("Starting ffmpeg update…")
        task = FfmpegUpdateTask(proxy=self._current_proxy())
        task.signals.step.connect(self._on_ffmpeg_update_step)
        task.signals.finished.connect(self._on_ffmpeg_update_finished)
        self._ffmpeg_update_task = task
        QThreadPool.globalInstance().start(task)

    # Logs one line of update progress as it happens (see update_ffmpeg's log callback)
    def _on_ffmpeg_update_step(self, message):
        self._log(message)

    # Reports the result of _start_ffmpeg_update back on the GUI thread: refreshes
    # the displayed ffmpeg version and updates the tree-style status line, same as
    # _on_ytdlp_update_finished.
    def _on_ffmpeg_update_finished(self, success, output, new_version):
        self._ffmpeg_update_task = None
        self.about_ffmpeg_version_label.setText(
            f"ffmpeg version: {_ffmpeg_version_display(new_version)}" if new_version else "ffmpeg version: not found"
        )
        self._log(f"ffmpeg update {'succeeded' if success else 'failed'}")
        if success:
            self.about_ffmpeg_update_text_label.setText("└── up to date")
            self.about_ffmpeg_update_link_label.setText("")
        else:
            self.about_ffmpeg_update_text_label.setText("└── update failed - see log")
            self.about_ffmpeg_update_link_label.setText(
                f'<a href="update" style="color: {BORDER_FOCUS}; text-decoration: underline;">click to retry</a>'
            )

    # Same idea as _start_ytdlp_update_check, but for the app's own version. There's
    # no update task to trigger yet - see get_latest_app_version/APP_LATEST_RELEASE_URL,
    # which will be filled in once the app has somewhere to publish releases to.
    def _start_app_update_check(self):
        self.about_app_update_text_label.setText("└── checking for updates…")
        self.about_app_update_link_label.setText("")
        task = AppUpdateCheckTask(proxy=self._current_proxy())
        task.signals.finished.connect(self._on_app_update_check_finished)
        QThreadPool.globalInstance().start(task)

    # Reports the result of _start_app_update_check back on the GUI thread
    def _on_app_update_check_finished(self, latest_version):
        if not latest_version:
            self.about_app_update_text_label.setText("└── could not check for updates")
            self.about_app_update_link_label.setText(
                f'<a href="check" style="color: {BORDER_FOCUS}; text-decoration: underline;">click to retry</a>'
            )
        elif latest_version == APP_VERSION:
            self.about_app_update_text_label.setText("└── up to date")
            self.about_app_update_link_label.setText("")
        else:
            self.about_app_update_text_label.setText(f"└── new version available: {latest_version}")
            self.about_app_update_link_label.setText("")

    # Handles the "click to retry" link next to the app-version tree-style status
    # line (there's no "update" link yet - see _on_app_update_check_finished)
    def _on_app_update_link_clicked(self, href):
        if href == "check":
            self._start_app_update_check()

    # Checked once per launch (see main()): this app no longer ships yt-dlp/ffmpeg
    # inside its own .exe (see _bundled_bin_dir), so a fresh install starts out
    # with neither in the ytdlp-bin folder. If either is missing, prompt instead of
    # letting the first probe/download silently fail.
    def _check_required_binaries_on_startup(self):
        missing = []
        if not _ytdlp_bin_path().is_file():
            missing.append("yt-dlp")
        if not _ffmpeg_bin_path().is_file():
            missing.append("ffmpeg")
        if missing:
            self._show_missing_binaries_dialog(missing)

    # Builds and shows the popup itself. "yt-dlp" and "ffmpeg" in the message are
    # clickable links to the same release pages this app's own updater pulls from
    # (see _on_missing_binaries_link_clicked); "Download" runs the same
    # download/update tasks the About tab's own "click to update"/"click to
    # download" links use (_start_ytdlp_update/_start_ffmpeg_update) for whichever
    # of the two is actually missing.
    def _show_missing_binaries_dialog(self, missing):
        dialog = QDialog(self)
        dialog.setWindowTitle("yt-dlp / ffmpeg required")
        dialog.setMinimumWidth(420)
        layout = QVBoxLayout(dialog)
        layout.setSpacing(layout.spacing() // 2)

        label = QLabel(
            "This program requires "
            f'<a href="yt-dlp" style="color: {BORDER_FOCUS};">yt-dlp</a> and '
            f'<a href="ffmpeg" style="color: {BORDER_FOCUS};">ffmpeg</a> to '
            "function. Press download to get it automatically. You can also get "
            "it from the about page updater or place it manually in "
            f"{_bundled_bin_dir()}"
        )
        label.setTextFormat(Qt.RichText)
        label.setWordWrap(True)
        label.setTextInteractionFlags(Qt.LinksAccessibleByMouse)
        label.setOpenExternalLinks(False)
        label.linkActivated.connect(self._on_missing_binaries_link_clicked)
        layout.addWidget(label)

        missing_label = QLabel(f"Missing: {', '.join(missing)}")
        missing_label.setWordWrap(True)
        layout.addWidget(missing_label)

        hint_label = QLabel(
            "Tip: You can also manually drop "
            f'<a href="yt-dlp-nightly" style="color: {BORDER_FOCUS};">nightly builds</a> '
            "there."
        )
        hint_label.setTextFormat(Qt.RichText)
        hint_label.setWordWrap(True)
        hint_label.setTextInteractionFlags(Qt.LinksAccessibleByMouse)
        hint_label.setOpenExternalLinks(False)
        hint_label.linkActivated.connect(self._on_missing_binaries_link_clicked)
        layout.addWidget(hint_label)

        button_row = QHBoxLayout()
        button_row.addStretch(1)
        close_btn = QPushButton("Close")
        close_btn.clicked.connect(dialog.reject)
        download_btn = QPushButton("Download")
        download_btn.setDefault(True)

        def _on_download_clicked():
            if "yt-dlp" in missing:
                self._start_ytdlp_update()
            if "ffmpeg" in missing:
                self._start_ffmpeg_update()
            dialog.accept()

        download_btn.clicked.connect(_on_download_clicked)
        button_row.addWidget(download_btn)
        button_row.addWidget(close_btn)
        layout.addLayout(button_row)

        dialog.exec()

    # Opens the yt-dlp/ffmpeg/nightly-builds release page (whichever link in the
    # missing-binaries popup was clicked - see _show_missing_binaries_dialog) in
    # the user's default browser. yt-dlp/ffmpeg are the same pages the About tab's
    # own version checks compare against (see
    # _YTDLP_RELEASES_PAGE_URL/_FFMPEG_RELEASES_PAGE_URL); the nightly-builds link
    # is a separate, manual-install-only option (_YTDLP_NIGHTLY_RELEASES_PAGE_URL).
    def _on_missing_binaries_link_clicked(self, href):
        url = {
            "yt-dlp": _YTDLP_RELEASES_PAGE_URL,
            "ffmpeg": _FFMPEG_RELEASES_PAGE_URL,
            "yt-dlp-nightly": _YTDLP_NIGHTLY_RELEASES_PAGE_URL,
        }.get(href)
        if url:
            QDesktopServices.openUrl(QUrl(url))

    # Create a form label and register it in the settings search index
    def _settings_label(self, text, tab_index):
        label = QLabel(text)
        label.setStyleSheet(sidebar_label_muted_style())
        self._form_labels.append(label)
        self._settings_search_index.append({"text": text, "tab_index": tab_index, "widget": label})
        return label

    # Build the URL input bar above the left panel
    def _build_url_widget(self):
        self.url_widget = QWidget()
        self.url_widget.setAttribute(Qt.WA_StyledBackground, True)
        self.url_widget.setStyleSheet(panel_style())
        layout = QVBoxLayout(self.url_widget)
        layout.setContentsMargins(1, 1, 1, 1)

        self.url_line_edit = SettingsSearchLineEdit()
        self.url_line_edit.setPlaceholderText(self._url_placeholder)
        self.url_line_edit.setStyleSheet(line_edit_style())
        layout.addWidget(self.url_line_edit)

        return self.url_widget

    # Build the right-hand sidebar stack (main sidebar plus one per settings tab)
    def _build_right_stack(self):
        self.right_stack = QStackedWidget()
        self.right_stack.addWidget(self._build_sidebar())
        self.right_stack.addWidget(self._build_settings_sidebar())
        return self.right_stack

    # Tab title shown in the shared settings sidebar for each settings tab, keyed
    # by settings_stack index (see _on_settings_tab_clicked)
    _SETTINGS_TAB_TITLES = ("General", "Connection", "Profiles", "Scheduler", "Plugins", "About")

    # Donation methods shown in the About tab's collapsible donate section, as
    # (title, copyable value) pairs - see _build_donate_row.
    _DONATE_METHODS = (
        ("Bitcoin", "bc1q8vwyhuxjwnlnp65n8n6x47gsud5mngar6a3avx"),
        ("ETH", "0x412eeD82a0F251a81eB69Dff951f0659Db9A5081"),
        ("USDT (ERC20)", "0x412eeD82a0F251a81eB69Dff951f0659Db9A5081"),
    )

    # Build the single settings sidebar panel shared by every settings tab (title,
    # separator, status info, OK/Apply/Cancel row). Its title updates to match
    # whichever tab is active instead of swapping in a whole new widget per tab -
    # see _on_settings_tab_clicked. Unlike the settings tab content, this sidebar is
    # a plain widget (not a scroll area) since it never needs to scroll.
    def _build_settings_sidebar(self):
        content = QWidget()
        content.setAttribute(Qt.WA_StyledBackground, True)
        content.setStyleSheet(panel_style())
        layout = QVBoxLayout(content)
        layout.setContentsMargins(10, 10, 10, 10)

        label = QLabel(APP_NAME)
        label.setStyleSheet(f"color: {TEXT_PRIMARY}; font-size: 14px; font-weight: bold;")
        layout.addWidget(label)
        self.settings_sidebar_label = label

        self.settings_profile_label = QLabel(f"Profile: {self._current_profile_name}")
        self.settings_profile_label.setStyleSheet(sidebar_label_muted_style())
        layout.addWidget(self.settings_profile_label)

        self.settings_status_label = QLabel("status: ready")
        self.settings_status_label.setStyleSheet(sidebar_label_muted_style())
        layout.addWidget(self.settings_status_label)

        separator = QLabel("―" * 20)
        separator.setAlignment(Qt.AlignCenter)
        separator.setStyleSheet(separator_style(margin_top=10))
        layout.addWidget(separator)
        self.settings_sidebar_separator = separator

        # A separate, static thumbnail placeholder - not the same widget as (or
        # synced with) the main sidebar's live preview, since there's nothing to
        # preview while the settings panel is open (the URL list isn't visible),
        # and it deliberately omits the title/channel/date/size details shown
        # under the main sidebar's thumbnail.
        settings_preview_label = QLabel("No preview")
        settings_preview_label.setFixedSize(260, 145)
        settings_preview_label.setAlignment(Qt.AlignCenter)
        settings_preview_label.setStyleSheet(
            f"background-color: {BG_THUMBNAIL}; border: 1px solid {BORDER_THUMBNAIL}; "
            f"color: {TEXT_FAINT};"
        )
        layout.addWidget(settings_preview_label, alignment=Qt.AlignHCenter)
        self.settings_sidebar_preview_label = settings_preview_label

        layout.addSpacing(20)

        self.settings_quality_label = QLabel("profile-wide quality:")
        self.settings_quality_label.setAlignment(Qt.AlignCenter)
        self.settings_quality_label.setStyleSheet(sidebar_label_muted_style())
        layout.addWidget(self.settings_quality_label)

        self.settings_proxy_label = QLabel("proxy:")
        self.settings_proxy_label.setAlignment(Qt.AlignCenter)
        self.settings_proxy_label.setStyleSheet(sidebar_label_muted_style())
        layout.addWidget(self.settings_proxy_label)

        self.settings_scheduler_label = QLabel("scheduler:")
        self.settings_scheduler_label.setAlignment(Qt.AlignCenter)
        self.settings_scheduler_label.setStyleSheet(sidebar_label_muted_style())
        layout.addWidget(self.settings_scheduler_label)

        self.settings_update_label = QLabel("update:")
        self.settings_update_label.setAlignment(Qt.AlignCenter)
        self.settings_update_label.setStyleSheet(sidebar_label_muted_style())
        layout.addWidget(self.settings_update_label)

        layout.addStretch()
        layout.addLayout(self._build_settings_action_row())

        self.settings_sidebar_content = content
        return content

    # Build the main sidebar (app name, version, status, preview, info lines)
    def _build_sidebar(self):
        self.sidebar_scroll = QScrollArea()
        self.sidebar_scroll.setWidgetResizable(True)
        self.sidebar_scroll.setFrameShape(QFrame.NoFrame)
        self.sidebar_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.sidebar_scroll.setStyleSheet(panel_style())
        self.sidebar_scroll.viewport().setStyleSheet(
            f"background-color: {BG_PANEL}; border: none;"
        )

        self.sidebar_panel = QWidget()
        self.sidebar_panel.setAttribute(Qt.WA_StyledBackground, True)
        self.sidebar_panel.setStyleSheet("background: transparent;")
        layout = QVBoxLayout(self.sidebar_panel)
        layout.setContentsMargins(10, 10, 10, 10)

        self.name_label = QLabel(APP_NAME)
        self.name_label.setStyleSheet(
            f"color: {TEXT_PRIMARY}; font-size: 14px; font-weight: bold;"
        )
        layout.addWidget(self.name_label)

        self.profile_label = QLabel(f"Profile: {self._current_profile_name}")
        self.profile_label.setStyleSheet(sidebar_label_muted_style())
        layout.addWidget(self.profile_label)

        self.status_label = QLabel("status: ready")
        self.status_label.setStyleSheet(sidebar_label_muted_style())
        layout.addWidget(self.status_label)

        self.separator = QLabel("―" * 20)
        self.separator.setAlignment(Qt.AlignCenter)
        self.separator.setStyleSheet(separator_style(margin_top=10))
        layout.addWidget(self.separator)

        self.preview_container = self._build_preview_container()
        layout.addWidget(self.preview_container)

        layout.addStretch()

        # Runtime and total size still left to download - every enabled link
        # that isn't already 100% complete (Reset makes a completed one count again)
        # - plus the combined speed of any downloads currently in progress; all kept
        # current by _update_sidebar_info()
        self.info_label_3 = QLabel("Runtime: 0:00")
        self.info_label_3.setAlignment(Qt.AlignCenter)
        self.info_label_3.setStyleSheet(sidebar_label_muted_style())
        layout.addWidget(self.info_label_3)

        self.info_label_1 = QLabel("Total size: 0mb")
        self.info_label_1.setAlignment(Qt.AlignCenter)
        self.info_label_1.setStyleSheet(sidebar_label_muted_style())
        layout.addWidget(self.info_label_1)

        self.info_label_2 = QLabel("Speed: 0.0 KB/s")
        self.info_label_2.setAlignment(Qt.AlignCenter)
        self.info_label_2.setStyleSheet(sidebar_label_muted_style())
        layout.addWidget(self.info_label_2)

        self.sidebar_scroll.setWidget(self.sidebar_panel)
        return self.sidebar_scroll

    # Build the thumbnail preview box with title/subtitle/detail labels
    def _build_preview_container(self):
        container = QWidget()
        c_layout = QVBoxLayout(container)
        c_layout.setContentsMargins(0, 0, 0, 0)
        c_layout.setAlignment(Qt.AlignHCenter | Qt.AlignVCenter)

        self.preview_label = QLabel()
        self.preview_label.setFixedSize(260, 145)
        self.preview_label.setAlignment(Qt.AlignCenter)
        self.preview_label.setText("No preview")
        self.preview_label.setStyleSheet(
            f"background-color: {BG_THUMBNAIL}; border: 1px solid {BORDER_THUMBNAIL}; "
            f"color: {TEXT_FAINT};"
        )
        c_layout.addWidget(self.preview_label, alignment=Qt.AlignHCenter)

        self.title_label = QLabel("")
        self.title_label.setAlignment(Qt.AlignCenter)
        self.title_label.setMaximumWidth(260)
        self.title_label.setStyleSheet(
            f"color: {TEXT_PRIMARY}; font-weight: bold; font-size: 12px;"
        )
        c_layout.addWidget(self.title_label, alignment=Qt.AlignHCenter)

        self.subtitle_label = QLabel("")
        self.subtitle_label.setAlignment(Qt.AlignCenter)
        self.subtitle_label.setMaximumWidth(260)
        self.subtitle_label.setStyleSheet(f"color: {TEXT_SECONDARY}; font-size: 10px;")
        c_layout.addWidget(self.subtitle_label, alignment=Qt.AlignHCenter)

        self.detail_label = QLabel("")
        self.detail_label.setAlignment(Qt.AlignCenter)
        self.detail_label.setMaximumWidth(260)
        self.detail_label.setStyleSheet(f"color: {TEXT_MUTED}; font-size: 10px;")
        c_layout.addWidget(self.detail_label, alignment=Qt.AlignHCenter)

        # Runtime ("M:SS"/"H:MM:SS"), shown only when yt-dlp reported one - hidden
        # entirely (rather than left blank) so it doesn't leave empty vertical space
        # under detail_label for links that don't have a duration (e.g. livestreams).
        self.duration_label = QLabel("")
        self.duration_label.setAlignment(Qt.AlignCenter)
        self.duration_label.setMaximumWidth(260)
        self.duration_label.setStyleSheet(f"color: {TEXT_MUTED}; font-size: 10px;")
        self.duration_label.setVisible(False)
        c_layout.addWidget(self.duration_label, alignment=Qt.AlignHCenter)

        return container

    # Build the bottom action row (Settings, Stop Probing, Download, Minimize Log, Exit)
    def _build_button_row(self):
        self.btn_settings = UnderlineButton("Settings", TEXT_SECONDARY, BORDER_FOCUS)
        self.btn_stop_probing = UnderlineButton("Stop Probing", TEXT_SECONDARY, BORDER_FOCUS)
        self.btn_download = UnderlineButton("Download", TEXT_SECONDARY, BORDER_FOCUS)
        self.btn_log_minimize = UnderlineButton("Minimize Log", TEXT_SECONDARY, BORDER_FOCUS)
        self.btn_refresh_channel = UnderlineButton("Refresh", TEXT_SECONDARY, BORDER_FOCUS)
        self.btn_exit = UnderlineButton("Exit", MEMBERS_ONLY_COLOR, MEMBERS_ONLY_COLOR)

        self.btn_settings.setIcon(QIcon(_flat_icon_path("settings", TEXT_SECONDARY)))
        self.btn_stop_probing.setIcon(QIcon(_flat_icon_path("eye", TEXT_SECONDARY)))
        self.btn_download.setIcon(QIcon(_flat_icon_path("download", TEXT_SECONDARY)))
        self.btn_refresh_channel.setIcon(QIcon(_flat_icon_path("refresh", TEXT_SECONDARY)))
        self.btn_log_minimize.setIcon(QIcon(_flat_icon_path("minimize", TEXT_SECONDARY)))
        self.btn_exit.setIcon(QIcon())
        for btn in (
            self.btn_settings, self.btn_stop_probing, self.btn_download,
            self.btn_log_minimize, self.btn_refresh_channel, self.btn_exit,
        ):
            btn.setIconSize(QSize(16, 16))

        for btn in (
            self.btn_settings, self.btn_stop_probing, self.btn_download,
            self.btn_log_minimize, self.btn_refresh_channel, self.btn_exit,
        ):
            btn.setMinimumWidth(80)
            btn.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Fixed)
        self.btn_log_minimize.hide()
        self.btn_stop_probing.setEnabled(False)
        self.btn_refresh_channel.setEnabled(False)

        self.session_status_label = QLabel("")
        self.session_status_label.setStyleSheet(sidebar_label_muted_style())
        self.session_status_label.setContentsMargins(0, 3, 0, 0)

        # Thin vertical divider separating Exit from the rest of the row - sized
        # to 85% of the row's height via stretch factors (15:170:15 => 170/200 = 85%)
        # rather than stretching edge-to-edge with the full row.
        exit_divider = QFrame()
        exit_divider.setFrameShape(QFrame.Shape.VLine)
        exit_divider.setFrameShadow(QFrame.Shadow.Plain)
        exit_divider.setFixedWidth(1)
        exit_divider.setStyleSheet(f"background-color: {BORDER_DISABLED}; border: none;")
        exit_divider_col = QVBoxLayout()
        exit_divider_col.setContentsMargins(0, 0, 0, 0)
        exit_divider_col.setSpacing(0)
        exit_divider_col.addStretch(15)
        exit_divider_col.addWidget(exit_divider, 170)
        exit_divider_col.addStretch(15)

        row = QHBoxLayout()
        row.setSpacing(6)
        row.addWidget(self.btn_settings)
        row.addWidget(self.btn_stop_probing)
        row.addWidget(self.btn_download)
        row.addWidget(self.btn_refresh_channel)
        row.addWidget(self.btn_log_minimize)
        row.addStretch()
        row.addWidget(self.session_status_label)
        row.addSpacing(12)
        row.addLayout(exit_divider_col)
        row.addSpacing(8)
        row.addWidget(self.btn_exit)
        return row


    # Update the "Proxy is active on <ip:port>" readout near the Exit button.
    # Only shown when the "Enable proxy" switch in Connection settings is on;
    # hidden entirely when proxy is disabled, so the row doesn't dedicate
    # space to an inactive readout. Called immediately whenever a proxy
    # setting changes.
    def _update_session_status_label(self):
        if self.chk_proxy.isChecked():
            host = self.proxy_host_edit.text().strip() or "no host set"
            proxy_text = f"Proxy is active on {host}:{self.proxy_port_spin.value()}"
            self.session_status_label.setText(proxy_text)
            self.session_status_label.setVisible(True)
        else:
            self.session_status_label.setVisible(False)

    # Wire up top-level widget signals to their handlers
    def _connect_signals(self):
        self.btn_settings.clicked.connect(self._toggle_settings)
        self.btn_stop_probing.clicked.connect(self._on_stop_probing_clicked)
        self.btn_download.clicked.connect(self._on_download_button_clicked)
        self.btn_log_minimize.clicked.connect(self._toggle_log_maximized)
        self.btn_refresh_channel.clicked.connect(self._on_refresh_channel_clicked)
        self.btn_exit.clicked.connect(self.close)
        self.url_line_edit.returnPressed.connect(self._on_url_entered)
        self.chk_proxy.stateChanged.connect(self._update_session_status_label)
        self.proxy_host_edit.textChanged.connect(self._update_session_status_label)
        self.proxy_port_spin.valueChanged.connect(self._update_session_status_label)
        self.chk_proxy.stateChanged.connect(self._update_settings_sidebar_info)
        self.proxy_host_edit.textChanged.connect(self._update_settings_sidebar_info)
        self.proxy_port_spin.valueChanged.connect(self._update_settings_sidebar_info)
        self.quality_combo.currentTextChanged.connect(self._update_settings_sidebar_info)
        self.scheduler_start_time_edit.timeChanged.connect(self._update_settings_sidebar_info)
        self.scheduler_stop_time_edit.timeChanged.connect(self._update_settings_sidebar_info)
        self._update_session_status_label()
        self.url_line_edit.textChanged.connect(self._on_url_text_changed)
        self.url_line_edit.focusLost.connect(self._on_url_line_edit_focus_lost)
        self.parallel_downloads_spin.valueChanged.connect(self._on_parallel_downloads_changed)
        self.url_list.itemSelectionChanged.connect(self._on_url_list_selection_changed)
        self.url_list.itemDoubleClicked.connect(self._on_url_list_item_double_clicked)
        self.url_list.itemClicked.connect(self._on_url_list_item_clicked)
        self.profile_combo.currentTextChanged.connect(self._on_profile_combo_changed)

        QApplication.instance().installEventFilter(self)

        self._update_download_button()

    # Installed app-wide so a click anywhere outside the link tree - another widget,
    # empty background, whatever - deselects whatever link/folder is currently
    # selected, the same way clicking empty space inside the tree already does.
    # Clicks inside the tree itself (including its scrollbar) are left alone since
    # QTreeWidget already handles its own selection there. Clicks that land in a
    # popup or dialog (context menu, confirm-removal, rename folder, file picker,
    # ...) are ignored too - those are separate top-level windows, and deselecting
    # out from under an in-progress menu/dialog action would be surprising.
    def eventFilter(self, obj, event):
        if event.type() == QEvent.MouseButtonPress and isinstance(obj, QWidget):
            if obj.window() is self and obj is not self.url_list \
                    and not self.url_list.isAncestorOf(obj) \
                    and self.url_list.selectedItems():
                self.url_list.clearSelection()
                self.url_list.setCurrentItem(None)
        return super().eventFilter(obj, event)
    # Open Settings, or close it - confirming whether to save, discard, or cancel
    # first if there are unsaved changes
    def _toggle_settings(self):
        if self.left_stack.currentIndex() == 0:
            self._open_settings()
        else:
            if self._snapshot_settings() != self.settings_committed:
                choice = self._confirm_unsaved_settings()
                if choice == QMessageBox.Cancel:
                    return
                if choice == QMessageBox.Save:
                    self._commit_settings()
                else:
                    self._restore_settings(self.settings_committed)
            else:
                self._restore_settings(self.settings_committed)
            self._close_settings()

    # Warn about unsaved settings changes before closing the settings panel without
    # an explicit OK/Apply (e.g. via the Settings toggle button), rather than
    # silently discarding them. Returns the QMessageBox.Save/Discard/Cancel role
    # the user picked.
    def _confirm_unsaved_settings(self):
        box = QMessageBox(self)
        box.setIcon(QMessageBox.Warning)
        box.setWindowTitle("Unsaved changes")
        box.setText("You have unsaved settings changes. Save them before closing?")
        box.setStandardButtons(QMessageBox.Save | QMessageBox.Discard | QMessageBox.Cancel)
        box.setDefaultButton(QMessageBox.Save)
        return box.exec()

    # Switch to the settings panel and enter settings-search mode
    def _open_settings(self):
        self.left_stack.setCurrentIndex(1)
        self.right_stack.setCurrentIndex(1)
        self._enter_settings_search_mode()
        self.btn_settings.set_active(True)
        self.btn_stop_probing.hide()
        self.btn_download.hide()
        self.btn_refresh_channel.hide()

    # Switch back to the URL list panel and exit settings-search mode
    def _close_settings(self):
        self.left_stack.setCurrentIndex(0)
        self.right_stack.setCurrentIndex(0)
        self._exit_settings_search_mode()
        self.btn_settings.set_active(False)
        self.btn_stop_probing.show()
        self.btn_download.show()
        self.btn_refresh_channel.show()

    # Switch straight to the About settings tab - used by the log's "updates
    # available" link (see _on_ytdlp_update_check_finished/_on_log_anchor_clicked)
    def _open_settings_about_tab(self):
        self.settings_tab_group.button(5).setChecked(True)
        self._on_settings_tab_clicked(5)
        self._open_settings()

    # Handles clicks on any hyperlink embedded in the log (currently just the
    # yt-dlp "updates available" notice)
    def _on_log_anchor_clicked(self, url):
        if url.toString() == "ytdlp-update":
            self._open_settings_about_tab()


    # Read the current value of every registered settings control into a dict
    def _snapshot_settings(self):
        return {
            key: getter(widget) for key, widget, getter, setter in self.settings_controls
        }

    # Write a settings snapshot back into all registered controls without firing signals
    def _restore_settings(self, snapshot):
        for key, widget, getter, setter in self.settings_controls:
            widget.blockSignals(True)
            setter(widget, snapshot[key])
            widget.blockSignals(False)
        self.proxy_host_edit.setEnabled(self.chk_proxy.isChecked())
        self.proxy_port_spin.setEnabled(self.chk_proxy.isChecked())
        self.scheduler_start_time_edit.setEnabled(self.chk_scheduler_start.isChecked())
        self.scheduler_stop_time_edit.setEnabled(self.chk_scheduler_stop.isChecked())
        self._update_status_label()
        self._update_session_status_label()

    # Discover every profile from disk (migrating an old combined registry file
    # first, if one is still present) and point every path helper at whichever
    # profile was last active. Called before _build_ui() so the Profiles tab is
    # populated correctly from the start.
    def _load_profile_registry(self):
        _migrate_legacy_profiles_file()
        if load_profile_metadata(DEFAULT_PROFILE_NAME) is None:
            save_profile_metadata(DEFAULT_PROFILE_NAME, None, None)
        self._profiles = _discover_profiles()

        names = [p["name"] for p in self._profiles]
        last = load_last_profile_name()
        if last not in names:
            last = DEFAULT_PROFILE_NAME if DEFAULT_PROFILE_NAME in names else names[0]
            # The profile that was last active is gone (its folder was deleted
            # outside the program) - don't leave the stale name sitting in
            # last_profile.json, or it'll just keep pointing at nothing.
            save_last_profile_name(last)
        self._current_profile_name = last
        set_current_profile(last)

    # Persist which profile is currently active (not the profile list itself -
    # that's always read straight from disk, so there's nothing else to save here)
    def _save_profile_registry(self):
        save_last_profile_name(self._current_profile_name)

    # Load the previously-added plugin list from disk, dropping (and re-saving
    # without) any entry whose file has since gone missing or stopped starting
    # with PLUGIN_MARKER_COMMENT. Called before _build_ui() so the Plugins tab
    # list is populated correctly from the start.
    def _load_enabled_plugins_from_disk(self):
        plugins_dir = _plugins_dir()
        names = load_enabled_plugins()
        valid = [
            name for name in names
            if (plugins_dir / name).is_file() and _is_valid_plugin_file(plugins_dir / name)
        ]
        if valid != names:
            save_enabled_plugins(valid)
        self._enabled_plugins = valid

    # Baseline settings for a brand-new (non-Default) profile: Default's own saved
    # settings overlaid on the as-built widget defaults, so new profiles start out
    # matching Default rather than the bare app defaults
    def _new_profile_settings_baseline(self):
        snapshot = dict(self._default_settings_snapshot)
        data = _load_json_file(_dir_for_profile(DEFAULT_PROFILE_NAME) / SETTINGS_FILENAME)
        if isinstance(data, dict):
            for key, widget, getter, setter in self.settings_controls:
                if key in data:
                    snapshot[key] = data[key]
        return snapshot

    # Switch the active profile: stop in-flight probes/downloads, flush the outgoing
    # profile's state to disk, point every path helper at the new profile's folder,
    # and load its links/settings - materializing its files immediately if it's brand
    # new, rather than waiting for the first edit to create them.
    def _switch_profile(self, name):
        if name == self._current_profile_name:
            return
        if self.left_stack.currentIndex() != 0:
            self._restore_settings(self.settings_committed)
            self._close_settings()
        self._stop_all_probing()
        self._stop_all_downloads()
        self._commit_settings()
        self._save_links_to_disk()

        self._current_profile_name = name
        set_current_profile(name)
        is_new_profile = not _links_file_path().exists() and not _settings_file_path().exists()

        self.url_list.clear()
        self._clear_preview()
        self._download_speeds_kbps.clear()

        baseline = self._new_profile_settings_baseline() if is_new_profile else self._default_settings_snapshot
        self.settings_committed = dict(baseline)
        self._restore_settings(self.settings_committed)
        self._load_settings_from_disk()
        self._load_links_from_disk()

        if is_new_profile:
            _thumbnails_dir()
            profile = self._current_profile_dict()
            if profile and profile.get("type") == "Sub Group":
                for channel in profile.get("channels") or []:
                    self._get_or_create_subgroup_channel_folder(channel)
            self._renumber_url_list()
            save_settings_file(self.settings_committed)

        self._sync_subgroup_folder_qualities()
        self._save_profile_registry()
        self._refresh_skip_visibility()
        self._update_sidebar_info()
        self._update_status_label()
        self._update_profile_label()
        self._update_url_line_edit_for_profile()
        self._update_download_button()
        self._update_refresh_button()
        self._update_ignore_title_pattern_visibility()
        self._update_quality_visibility()
        self._update_number_playlist_downloads_visibility()
        self._update_subgroup_channels_visibility()
        self._log(f"Switched to profile '{name}'")
        QMessageBox.information(self, "Profile switched", f"Switched to profile : {name}")

    # Re-scan every profile from disk - a profile folder may have been deleted (or a
    # backup copied back in) from outside the program since it was last loaded - and
    # refresh the combo/list to match. If the active profile itself was removed this
    # way, switch to Default (which always exists, since it's just the app folder).
    def _sync_profiles_with_disk(self):
        fresh = _discover_profiles()
        if fresh == self._profiles:
            return
        self._profiles = fresh
        names = [p["name"] for p in fresh]

        self.profile_combo.blockSignals(True)
        self.profile_combo.clear()
        self.profile_combo.addItems(names)
        self.profile_combo.blockSignals(False)

        if self._current_profile_name in names:
            self.profile_combo.setCurrentText(self._current_profile_name)
        else:
            # Not blocked: lets the normal combo-changed handler drive the switch
            self.profile_combo.setCurrentText(names[0] if DEFAULT_PROFILE_NAME not in names else DEFAULT_PROFILE_NAME)

        self._reload_profile_list()
        self._log("Profiles refreshed to match what's on disk")

    # Look up the active profile's own dict in the registry (name/type/channel_url)
    def _current_profile_dict(self):
        return next(
            (p for p in self._profiles if p["name"] == self._current_profile_name), None,
        )

    # The "Ignore pattern in title" setting only ever does anything for videos that
    # came from a standalone Channel or Playlist link (see
    # _ignore_title_pattern_for_item) - meaningless for the Default profile (no
    # type), a "Generic video" profile (every link is a standalone single video), a
    # "Generic file" profile (its downloads aren't titled videos with a
    # playlist/channel-supplied title at all), or a Sub Group (each channel inside
    # it is refreshed/tracked on its own, and this setting was never meant to reach
    # into that per-channel folder structure). Hide the row outright rather than
    # leave a setting visible that can't do anything for the profile currently open.
    def _update_ignore_title_pattern_visibility(self):
        profile = self._current_profile_dict()
        ptype = profile.get("type") if profile else None
        visible = ptype in ("Channel", "Playlist")
        self.ignore_pattern_label.setVisible(visible)
        self.ignore_title_pattern_edit.setVisible(visible)

    # The Quality setting only affects yt-dlp's video/audio format selection, which
    # doesn't apply to a "Generic file" profile - see probe_url/download_url's is_file
    # param. Hide the row outright there rather than leave a setting visible that
    # can't do anything for the profile currently open.
    def _update_quality_visibility(self):
        visible = not self._current_profile_is_generic_file()
        self._general_form.setRowVisible(self.quality_combo, visible)

    # "Number playlist downloads" only means anything for a profile whose links can
    # come from a playlist listing (where yt-dlp reports each entry's position in
    # it): a "Playlist" profile always can, and so can the Default profile since the
    # user might paste a playlist URL straight into it. A "Channel" profile's links
    # come from the channel's own upload order instead (see _renumber_url_list /
    # Refresh), not a playlist listing, so numbering doesn't apply there - nor to a
    # "Generic file"/"Generic video" profile, whose links are each standalone with no
    # ordering to preserve. Hide the checkbox outright rather than leave a setting
    # visible that can't do anything for the profile currently open.
    def _update_number_playlist_downloads_visibility(self):
        profile = self._current_profile_dict()
        ptype = profile.get("type") if profile else None
        self.chk_number_playlist_downloads.setVisible(ptype in (None, "Playlist"))

    # The Refresh button only makes sense for a profile that tracks an external
    # source it can re-check for new videos (a Channel, a Playlist, or a Sub Group's
    # channels) - hide it outright for any other profile type rather than leaving it
    # visible but dead. Within a Channel profile it's still only enabled once there's
    # an actual channel URL saved; within a Sub Group, once it has at least one
    # channel; either way, not while a refresh is already running.
    def _update_refresh_button(self):
        profile = self._current_profile_dict()
        ptype = profile.get("type") if profile else None
        settings_open = self.left_stack.currentIndex() == 1
        self.btn_refresh_channel.setVisible(
            not settings_open and ptype in ("Channel", "Playlist", "Sub Group")
        )
        refreshing = self._channel_refresh_task is not None
        if ptype == "Sub Group":
            has_source = bool(profile and any(c.get("url") for c in (profile.get("channels") or [])))
        elif ptype == "Playlist":
            has_source = bool(self._playlist_folders())
        else:
            has_source = bool(profile and ptype == "Channel" and profile.get("channel_url"))
        self.btn_refresh_channel.setText("Refresh")
        self.btn_refresh_channel.setEnabled(refreshing or has_source)
        self.btn_refresh_channel.set_active(refreshing)

    # Every top-level folder in the tree that was expanded from a playlist link (i.e.
    # carries a remembered PLAYLIST_SOURCE_URL_ROLE) - what a "Playlist" profile's
    # Refresh re-checks, one after another, for newly added videos.
    def _playlist_folders(self):
        folders = []
        for i in range(self.url_list.topLevelItemCount()):
            item = self.url_list.topLevelItem(i)
            if item.data(0, IS_FOLDER_ROLE) and item.data(0, PLAYLIST_SOURCE_URL_ROLE):
                folders.append(item)
        return folders

    # For a Channel profile, the URL bar isn't used to add links (those come from
    # "Refresh" instead) - lock it read-only and show the channel's own link as
    # placeholder/background text. A Sub Group profile works the same way, except
    # there's no single link to show, so the placeholder mentions its channel count
    # instead. Any other profile gets the normal, editable bar.
    def _update_url_line_edit_for_profile(self):
        profile = self._current_profile_dict()
        ptype = profile.get("type") if profile else None
        channel_url = profile.get("channel_url") if profile and ptype == "Channel" else None
        is_subgroup = ptype == "Sub Group"
        self.url_line_edit.setReadOnly(bool(channel_url) or is_subgroup)
        if is_subgroup:
            count = len(profile.get("channels") or [])
            self._url_placeholder = f"{count} channel(s) — press Refresh to check for new uploads"
        else:
            self._url_placeholder = (
                f"{channel_url} — press Refresh to start appending links"
                if channel_url else "Paste url(s) here ..."
            )
        if self.left_stack.currentIndex() != 1:
            self.url_line_edit.setPlaceholderText(self._url_placeholder)

    # "Refresh" button: re-fetch the active profile's tracked video listing(s) and
    # pull in anything uploaded since the last refresh, running each listing on a
    # worker thread so the UI stays responsive. A Channel profile has a single
    # source; a Sub Group has one per channel, and a Playlist profile has one per
    # playlist folder already in the tree - each refreshed one after another (see
    # _start_next_subgroup_channel_refresh/_start_next_playlist_refresh) since only
    # one listing runs at a time.
    def _on_refresh_channel_clicked(self):
        profile = self._current_profile_dict()
        if self._channel_refresh_task is not None:
            self._stop_refresh()
            return
        ptype = profile.get("type") if profile else None
        if ptype == "Sub Group":
            channels = [c for c in (profile.get("channels") or []) if c.get("url")]
            if not channels:
                self._log("Refresh: sub group has no channels")
                return
            self._subgroup_refresh_queue = self._channels_in_folder_tree_order(channels)
            self._subgroup_refresh_added_total = 0
            self._start_next_subgroup_channel_refresh()
            return

        if ptype == "Playlist":
            folders = self._playlist_folders()
            if not folders:
                self._log("Refresh: no playlist links to refresh yet")
                return
            self._playlist_refresh_queue = folders
            self._playlist_refresh_added_total = 0
            self._start_next_playlist_refresh()
            return

        channel_url = profile.get("channel_url") if profile else None
        if not channel_url:
            self._log("Refresh: active profile has no channel link")
            return
        task = ChannelRefreshTask(channel_url, self._existing_channel_video_ids(), self._current_proxy())
        task.signals.finished.connect(self._on_channel_refresh_finished)
        task.signals.error.connect(self._on_channel_refresh_error)
        self._channel_refresh_task = task
        self._refresh_task_started()
        self._update_refresh_button()
        self._probe_pool.start(task)
        self._log(f"Refreshing channel: {channel_url}")

    # Cancel whatever refresh is currently in flight (single channel, or the
    # current step of a Sub Group/Playlist refresh queue) and drop any further
    # queued steps, rather than letting it continue on to the next one
    def _stop_refresh(self):
        task = self._channel_refresh_task
        if task is None:
            return
        task.cancel()
        folder_item = getattr(task, "item", None)
        if folder_item is not None:
            self._tasks_by_item.pop(id(folder_item), None)
        self._channel_refresh_task = None
        self._subgroup_refresh_queue = []
        self._subgroup_refresh_active_channel = None
        self._playlist_refresh_queue = []
        self._refresh_task_finished()
        self._update_refresh_button()
        self._log("Stopped refresh")

    # Pop the next channel off the active Sub Group refresh queue and start listing
    # it, tagging it as the "active" subgroup channel so _on_channel_refresh_finished/
    # _on_channel_refresh_error know which folder to target and to keep the queue
    # moving afterward. Logs a final summary once the queue is empty.
    def _start_next_subgroup_channel_refresh(self):
        if not self._subgroup_refresh_queue:
            self._subgroup_refresh_active_channel = None
            self._update_refresh_button()
            self._log(
                f"Refresh: sub group finished, added {self._subgroup_refresh_added_total} "
                "new video(s) in total"
            )
            return
        channel = self._subgroup_refresh_queue.pop(0)
        self._subgroup_refresh_active_channel = channel
        folder = self._find_folder_by_name(channel.get("name"))
        existing_ids = self._existing_channel_video_ids_in_folder(folder)
        task = ChannelRefreshTask(channel.get("url"), existing_ids, self._current_proxy())
        task.signals.finished.connect(self._on_channel_refresh_finished)
        task.signals.error.connect(self._on_channel_refresh_error)
        self._channel_refresh_task = task
        self._refresh_task_started()
        self._update_refresh_button()
        self._probe_pool.start(task)
        self._log(f"Refreshing channel '{channel.get('name')}': {channel.get('url')}")

    # Pop the next playlist folder off the active Playlist-profile refresh queue and
    # start re-listing it (reusing PlaylistExpandTask - the same full-listing fetch
    # used to expand it in the first place, since a playlist has no guaranteed
    # newest-first order the way a channel's uploads tab does, so there's no early-
    # stop optimization to reuse here). New entries are diffed in and appended once
    # the listing is back - see _on_playlist_refresh_finished. Logs a final summary
    # once the queue is empty.
    def _start_next_playlist_refresh(self):
        if not self._playlist_refresh_queue:
            self._update_refresh_button()
            self._log(
                f"Refresh: finished, added {self._playlist_refresh_added_total} "
                "new video(s) in total"
            )
            return
        folder = self._playlist_refresh_queue.pop(0)
        url = folder.data(0, PLAYLIST_SOURCE_URL_ROLE)
        task = PlaylistExpandTask(folder, url, self._current_proxy())
        task.signals.finished.connect(self._on_playlist_refresh_finished)
        task.signals.error.connect(self._on_playlist_refresh_error)
        self._channel_refresh_task = task
        self._tasks_by_item[id(folder)] = task
        self._refresh_task_started()
        self._update_refresh_button()
        self._probe_pool.start(task)
        self._log(f"Refreshing playlist '{folder.data(0, RAW_TEXT_ROLE)}': {url}")

    # Handle a completed playlist-refresh listing: append any entries not already
    # present anywhere in the tree into the existing folder (numbered by their
    # current position in the listing, same as a fresh expand), then move on to the
    # next queued playlist folder (if any)
    def _on_playlist_refresh_finished(self, folder_item, info):
        self._channel_refresh_task = None
        self._tasks_by_item.pop(id(folder_item), None)
        self._refresh_task_finished()
        title = folder_item.data(0, RAW_TEXT_ROLE) or "playlist"
        entries = info.get("entries") or []
        if not entries:
            self._log(f"Refresh: playlist listing for '{title}' came back empty")
            self._update_refresh_button()
            self._start_next_playlist_refresh()
            return

        existing = self._existing_urls()
        new_items = []
        for position, url in enumerate(entries, start=1):
            if url in existing:
                continue
            existing.add(url)
            item = QTreeWidgetItem()
            item.setData(0, LINK_UUID_ROLE, str(uuid.uuid4()))
            item.setData(0, URL_ROLE, url)
            item.setData(0, RAW_TEXT_ROLE, url)
            item.setData(0, PLAYLIST_INDEX_ROLE, position)
            self._apply_item_flags(item)
            folder_item.addChild(item)
            new_items.append(item)

        if not new_items:
            self._log(f"Refresh: no new videos since last check for '{title}'")
            self._update_refresh_button()
            self._start_next_playlist_refresh()
            return

        folder_item.setExpanded(True)
        for item in new_items:
            self._log_url_added(item, item.data(0, URL_ROLE))
        self._renumber_url_list()
        self._log(f"Refresh: added {len(new_items)} new video(s) to '{title}'")
        self._playlist_refresh_added_total += len(new_items)
        for item in new_items:
            self._start_probe(item)

        self._update_refresh_button()
        self._start_next_playlist_refresh()

    # Handle a failed playlist refresh: log it and move on to the next queued
    # playlist folder (if any)
    def _on_playlist_refresh_error(self, folder_item, message):
        self._channel_refresh_task = None
        self._tasks_by_item.pop(id(folder_item), None)
        self._refresh_task_finished()
        title = folder_item.data(0, RAW_TEXT_ROLE) or "playlist"
        self._log(f"Refresh failed for '{title}': {message}")
        self._update_refresh_button()
        self._start_next_playlist_refresh()

    # yt-dlp lists a channel's "/videos" tab newest-first, so entries are walked in
    # that order and collection stops at the first video already in the tree (matched
    # by video ID, not URL text - see fetch_channel_new_entries) - assumed to be the
    # newest video from the last refresh, meaning everything after it (in this
    # listing) has already been added. New links are then inserted at the very
    # top of the tree, newest first, and probing starts for each of them.
    # Find the active Channel profile's folder in the tree (a top-level folder item
    # named after the profile), creating it at the top if it doesn't exist yet
    def _get_or_create_channel_folder(self):
        profile = self._current_profile_dict()
        name = profile["name"] if profile else self._current_profile_name
        return self._get_or_create_named_folder(name)

    # Generic version of _get_or_create_channel_folder: find (or create, at the top
    # of the tree) a top-level folder with the given name. Used both for a Channel
    # profile's own folder (named after the profile) and for each of a Sub Group
    # profile's channel folders (named after the channel).
    def _get_or_create_named_folder(self, name):
        folder = self._find_folder_by_name(name)
        if folder is not None:
            return folder
        folder = QTreeWidgetItem()
        folder.setData(0, IS_FOLDER_ROLE, True)
        folder.setData(0, RAW_TEXT_ROLE, name)
        folder.setData(0, URL_ROLE, None)
        folder.setData(0, LINK_UUID_ROLE, None)
        self._apply_item_flags(folder)
        self.url_list.insertTopLevelItem(0, folder)
        return folder

    # Find a top-level folder by name without creating it. Returns None if there
    # isn't one.
    def _find_folder_by_name(self, name):
        for i in range(self.url_list.topLevelItemCount()):
            item = self.url_list.topLevelItem(i)
            if item.data(0, IS_FOLDER_ROLE) and item.data(0, RAW_TEXT_ROLE) == name:
                return item
        return None

    # Sort a Sub Group's channels to match their folders' top-to-bottom order in
    # the tree, rather than the order they were added to the profile - used to
    # queue a Sub Group refresh so it visibly proceeds down the list. A channel
    # whose folder doesn't exist yet (nothing refreshed for it so far) has no
    # tree position to sort by, so it's placed after every channel that does,
    # keeping those un-foldered channels in their original relative order.
    def _channels_in_folder_tree_order(self, channels):
        folder_order = {
            self.url_list.topLevelItem(i).data(0, RAW_TEXT_ROLE): i
            for i in range(self.url_list.topLevelItemCount())
            if self.url_list.topLevelItem(i).data(0, IS_FOLDER_ROLE)
        }
        no_folder = len(folder_order)
        return sorted(
            channels, key=lambda c: folder_order.get(c.get("name"), no_folder)
        )

    # Re-stamp FOLDER_QUALITY_ROLE onto every Sub Group channel folder currently in
    # the tree from that channel's own "quality" entry in the profile's "channels"
    # metadata (the actual source of truth - a folder's role is just a fast, local
    # mirror of it for _quality_for_item/the sidebar preview to read). Cheap, so it's
    # safe to call defensively any time the tree or the channels list might have
    # drifted out of sync with each other (profile switch, refresh, editing a
    # channel's quality). No-op for any non-Sub-Group profile.
    def _sync_subgroup_folder_qualities(self):
        profile = self._current_profile_dict()
        if not profile or profile.get("type") != "Sub Group":
            return
        quality_by_name = {
            c.get("name"): c.get("quality") for c in (profile.get("channels") or [])
        }
        for i in range(self.url_list.topLevelItemCount()):
            folder = self.url_list.topLevelItem(i)
            if folder.data(0, IS_FOLDER_ROLE):
                name = folder.data(0, RAW_TEXT_ROLE)
                if name in quality_by_name:
                    folder.setData(0, FOLDER_QUALITY_ROLE, quality_by_name[name])

    # Same as _get_or_create_named_folder, but for a Sub Group channel specifically:
    # also stamps the freshly-found-or-created folder's FOLDER_QUALITY_ROLE from
    # that channel's "quality" metadata, so a brand-new folder (this channel's very
    # first Refresh) starts out with the right quality already applied rather than
    # waiting for the next _sync_subgroup_folder_qualities() pass.
    def _get_or_create_subgroup_channel_folder(self, channel):
        folder = self._get_or_create_named_folder(channel.get("name"))
        folder.setData(0, FOLDER_QUALITY_ROLE, channel.get("quality"))
        return folder

    # Handle a completed channel-refresh listing: add any new entries, then move
    # on to the next queued sub group channel (if any)
    def _on_channel_refresh_finished(self, info):
        self._channel_refresh_task = None
        self._refresh_task_finished()
        self._sync_subgroup_folder_qualities()

        active_channel = self._subgroup_refresh_active_channel
        self._subgroup_refresh_active_channel = None
        label = f" for '{active_channel['name']}'" if active_channel else ""

        entries = info.get("entries") or []
        if not entries:
            self._log(f"Refresh: channel listing{label} came back empty")
            self._update_refresh_button()
            if active_channel is not None:
                self._start_next_subgroup_channel_refresh()
            return

        if active_channel is not None:
            folder = self._get_or_create_subgroup_channel_folder(active_channel)
            existing_ids = self._existing_channel_video_ids_in_folder(folder)
        else:
            folder = self._get_or_create_channel_folder()
            existing_ids = self._existing_channel_video_ids()

        new_urls = []
        for url in entries:
            if _youtube_video_id(url) in existing_ids:
                break
            new_urls.append(url)

        if not new_urls:
            self._log(f"Refresh: no new videos since last check{label}")
            self._update_refresh_button()
            if active_channel is not None:
                self._start_next_subgroup_channel_refresh()
            return

        new_items = []
        for url in reversed(new_urls):
            item = QTreeWidgetItem()
            item.setData(0, LINK_UUID_ROLE, str(uuid.uuid4()))
            item.setData(0, URL_ROLE, url)
            item.setData(0, RAW_TEXT_ROLE, url)
            self._apply_item_flags(item)
            folder.insertChild(0, item)
            new_items.append(item)
        new_items.reverse()
        folder.setExpanded(True)
        for item in new_items:
            self._log_url_added(item, item.data(0, URL_ROLE))

        self._renumber_url_list()
        self._log(f"Refresh: added {len(new_items)} new video(s){label}")
        if active_channel is not None:
            self._subgroup_refresh_added_total += len(new_items)
            # A Sub Group refresh only lists each channel's links and files them
            # into that channel's own folder right away - it deliberately doesn't
            # also probe every new link (fetching each one's title/thumbnail/size),
            # since that would compete with the other queued channels' own listing
            # requests for the same worker pool and stall the queue. Probing is
            # left manual (see "Retry probe" in the tree's context menu) so the
            # whole sub group can move from one channel's folder to the next
            # immediately.
        else:
            for item in new_items:
                self._start_probe(item)

        self._update_refresh_button()
        if active_channel is not None:
            self._start_next_subgroup_channel_refresh()

    # Handle a failed channel refresh: log it and move on to the next queued
    # sub group channel (if any)
    def _on_channel_refresh_error(self, message):
        self._channel_refresh_task = None
        self._refresh_task_finished()
        active_channel = self._subgroup_refresh_active_channel
        self._subgroup_refresh_active_channel = None
        label = f" for '{active_channel['name']}'" if active_channel else ""
        self._log(f"Refresh failed{label}: {message}")
        self._update_refresh_button()
        if active_channel is not None:
            self._start_next_subgroup_channel_refresh()

    # Load settings from disk (if any) and apply them to the UI on startup
    def _load_settings_from_disk(self):
        data = load_settings_file()
        if not data:
            return
        snapshot = dict(self.settings_committed)
        for key, widget, getter, setter in self.settings_controls:
            if key in data:
                snapshot[key] = data[key]
        try:
            self._restore_settings(snapshot)
        except (TypeError, ValueError):
            return
        self.settings_committed = self._snapshot_settings()
        self._refresh_theme_styles()

    # Persist the current settings to disk
    def _commit_settings(self):
        if self.chk_detailed_log.isChecked() != self.settings_committed["detailed_log"]:
            self._log(f"Detailed log: {'on' if self.chk_detailed_log.isChecked() else 'off'}")
        self.settings_committed = self._snapshot_settings()
        save_settings_file(self.settings_committed)

    # Commit settings and close the settings panel
    def _on_settings_ok(self):
        self._commit_settings()
        self._close_settings()

    # Commit settings without closing the settings panel
    def _on_settings_apply(self):
        self._commit_settings()

    # Discard changes and close the settings panel
    def _on_settings_cancel(self):
        self._restore_settings(self.settings_committed)
        self._close_settings()


    # Clear the URL bar and repurpose it as a settings search box
    def _enter_settings_search_mode(self):
        self.url_line_edit.blockSignals(True)
        self.url_line_edit.clear()
        self.url_line_edit.blockSignals(False)
        self._prev_url_text = ""
        self.url_line_edit.setReadOnly(False)
        self.url_line_edit.setPlaceholderText("Search settings...")

    # Clear any search highlight and restore the URL bar's normal placeholder
    def _exit_settings_search_mode(self):
        self._clear_settings_search_highlight()
        self.url_line_edit.blockSignals(True)
        self.url_line_edit.clear()
        self.url_line_edit.blockSignals(False)
        self._prev_url_text = ""
        self._update_url_line_edit_for_profile()

    # Find and highlight the first settings row matching the search text
    def _on_settings_search(self, text):
        self._clear_settings_search_highlight()
        query = text.strip().lower()
        if len(query) < 3:
            return
        for entry in self._settings_search_index:
            if query in entry["text"].lower():
                self._highlight_settings_match(entry)
                break

    # Switch to the matched setting's tab and apply the highlight style to it
    def _highlight_settings_match(self, entry):
        self.settings_tab_group.button(entry["tab_index"]).setChecked(True)
        self._on_settings_tab_clicked(entry["tab_index"])
        widget = entry["widget"]
        self._settings_search_highlight = widget
        self._settings_search_highlight_original = widget.styleSheet()
        widget.setStyleSheet(settings_search_highlight_style())

    # Remove any active settings-search highlight and restore the widget's normal style
    def _clear_settings_search_highlight(self):
        if self._settings_search_highlight is not None:
            self._settings_search_highlight.setStyleSheet(self._settings_search_highlight_original)
            self._settings_search_highlight = None
            self._settings_search_highlight_original = None

    # Clear the settings search box when it loses focus while settings is open
    def _on_url_line_edit_focus_lost(self):
        if self.left_stack.currentIndex() != 1:
            return
        self.url_line_edit.blockSignals(True)
        self.url_line_edit.clear()
        self.url_line_edit.blockSignals(False)
        self._prev_url_text = ""
        self._clear_settings_search_highlight()

    # Handle Enter in the URL bar: add any URLs in the text and clear the field
    def _on_url_entered(self):
        if self.left_stack.currentIndex() == 1 or self.url_line_edit.isReadOnly():
            return
        text = self.url_line_edit.text().strip()
        if text:
            self._add_urls_from_text(text)
            self.url_line_edit.clear()
        self._prev_url_text = ""

    # Route typing to settings search when settings is open, or auto-add pasted URLs otherwise
    def _on_url_text_changed(self, text):
        if self.left_stack.currentIndex() == 1:
            self._on_settings_search(text)
            self._prev_url_text = text
            return
        if self.url_line_edit.isReadOnly():
            return
        if len(text) - len(self._prev_url_text) > 1:
            self._add_urls_from_text(text)
            self.url_line_edit.blockSignals(True)
            self.url_line_edit.clear()
            self.url_line_edit.blockSignals(False)
            text = ""
        self._prev_url_text = text

    # Collect the URLs of every link already in the tree (recursing into folders),
    # used to silently drop duplicate pastes
    def _existing_urls(self):
        urls = set()

        # Recursively collect every url already present under this item
        def visit(item):
            if item.data(0, IS_FOLDER_ROLE):
                for i in range(item.childCount()):
                    visit(item.child(i))
            elif item.data(0, IS_LOAD_MORE_ROLE):
                urls.update(_collect_urls_from_nodes(item.data(0, LOAD_MORE_NODES_ROLE) or []))
            else:
                url = item.data(0, URL_ROLE)
                if url:
                    urls.add(url)

        for i in range(self.url_list.topLevelItemCount()):
            visit(self.url_list.topLevelItem(i))
        return urls

    # Like _existing_urls, but reduced to bare YouTube video IDs rather than full URL
    # strings - used for channel-refresh matching, since two mentions of the same
    # video can legitimately have different URL text (see fetch_channel_new_entries).
    # Non-YouTube links (no video ID) are silently dropped, since a channel refresh
    # only ever produces YouTube video URLs to match against.
    def _existing_channel_video_ids(self):
        ids = set()
        for url in self._existing_urls():
            video_id = _youtube_video_id(url)
            if video_id:
                ids.add(video_id)
        return ids

    # Like _existing_channel_video_ids, but scoped to a single folder's direct
    # children rather than the whole tree - used for a Sub Group's per-channel
    # refresh, so that one channel's videos never affect where another channel's
    # refresh stops. Returns an empty set if the folder doesn't exist yet.
    def _existing_channel_video_ids_in_folder(self, folder):
        ids = set()
        if folder is None:
            return ids
        for i in range(folder.childCount()):
            video_id = _youtube_video_id(folder.child(i).data(0, URL_ROLE) or "")
            if video_id:
                ids.add(video_id)
        return ids

    # Extract URLs from text and add each as a tree item, assigning every new link a UUID
    # and skipping any URL already present in the tree. Anything in the pasted text that
    # isn't an actual http(s) URL is ignored (see _extract_urls). A playlist URL (see
    # _is_playlist_url) is added the same as any other link, then converted into a folder
    # in place once its listing comes back (_on_playlist_expanded).
    def _add_urls_from_text(self, text):
        urls = _extract_urls(text)
        if not urls:
            self._log("Nothing pasted looked like a valid link")
            return
        # A channel link is a worse fit for the Default profile (no tracking/refresh
        # support) - warn and let the user bail out to Settings > Profiles *before*
        # anything is actually added. Only "Ignore" lets the paste continue below.
        if self._current_profile_name == DEFAULT_PROFILE_NAME and any(
            _is_channel_url(url) for url in urls
        ):
            if not self._confirm_channel_link_in_default_profile():
                return
        existing = self._existing_urls()
        new_items = []
        skipped = 0
        for url in urls:
            if url in existing:
                skipped += 1
                continue
            existing.add(url)
            item = QTreeWidgetItem()
            item.setData(0, LINK_UUID_ROLE, str(uuid.uuid4()))
            item.setData(0, URL_ROLE, url)
            item.setData(0, RAW_TEXT_ROLE, url)
            self._apply_item_flags(item)
            self.url_list.addTopLevelItem(item)
            new_items.append(item)
            self._log_url_added(item, url)
        if new_items:
            self._renumber_url_list()
            self._update_download_button()
        if skipped:
            self._log(f"Skipped {skipped} duplicate link(s)")
        for item in new_items:
            if _is_playlist_url(item.data(0, URL_ROLE)):
                self._start_playlist_expand(item)
            else:
                self._start_probe(item)

    # Nudge shown *before* a channel link is added while the Default profile is active -
    # a dedicated Channel profile is what actually supports tracking/refreshing new
    # uploads, so the Default profile is a worse fit even though the link would still
    # work. Returns True if the paste should go ahead (i.e. "Ignore" was chosen);
    # returns False - and jumps to Settings > Profiles - if "Go to profile selection"
    # was chosen, in which case the link is never added.
    def _confirm_channel_link_in_default_profile(self):
        box = QMessageBox(self)
        box.setIcon(QMessageBox.Warning)
        box.setWindowTitle("Channel link in Default profile")
        box.setText(
            "This looks like a channel link. For a better experience - including "
            "tracking and refreshing new uploads - consider using a dedicated "
            "Channel profile instead of Default."
        )
        btn_goto = box.addButton("Go to profile selection", QMessageBox.AcceptRole)
        box.addButton("Ignore", QMessageBox.RejectRole)
        box.setDefaultButton(btn_goto)
        box.exec()
        if box.clickedButton() == btn_goto:
            self._open_settings()
            self.settings_tab_group.button(2).setChecked(True)
            self._on_settings_tab_clicked(2)
            return False
        return True

    # Queue a yt-dlp playlist listing for a link item that was just added as a playlist URL;
    # once it resolves, _on_playlist_expanded turns that same item into a folder in place
    def _start_playlist_expand(self, item):
        url = item.data(0, URL_ROLE)
        if not url or item.data(0, LINK_DISABLED_ROLE):
            return
        task = PlaylistExpandTask(item, url, self._current_proxy())
        task.signals.finished.connect(self._on_playlist_expanded)
        task.signals.error.connect(self._on_playlist_expand_error)
        self._tasks_by_item[id(item)] = task
        self._probe_started()
        self._probe_pool.start(task)

    # Turn a playlist link item into a folder in place, named after the playlist, and add
    # each of its (non-duplicate) entries inside it as a link, then start probing them
    def _on_playlist_expanded(self, item, info):
        self._tasks_by_item.pop(id(item), None)
        title = info.get("title") or "Playlist"
        entries = info.get("entries") or []
        if not entries:
            self._on_playlist_expand_error(item, "playlist has no videos")
            return

        existing = self._existing_urls()
        existing.discard(item.data(0, URL_ROLE))
        to_add = []
        skipped = 0
        for position, url in enumerate(entries, start=1):
            if url in existing:
                skipped += 1
                continue
            existing.add(url)
            to_add.append((position, url))
        if not to_add:
            self._on_playlist_expand_error(item, f"all {skipped} link(s) already added")
            return

        source_url = item.data(0, URL_ROLE)
        item.setData(0, IS_FOLDER_ROLE, True)
        item.setData(0, RAW_TEXT_ROLE, title)
        item.setData(0, URL_ROLE, None)
        item.setData(0, LINK_UUID_ROLE, None)
        item.setData(0, PROBE_FAILED_ROLE, False)
        item.setData(0, PLAYLIST_SOURCE_URL_ROLE, source_url)
        self._apply_item_flags(item)

        new_items = []
        for position, url in to_add:
            child = QTreeWidgetItem()
            child.setData(0, LINK_UUID_ROLE, str(uuid.uuid4()))
            child.setData(0, URL_ROLE, url)
            child.setData(0, RAW_TEXT_ROLE, url)
            child.setData(0, PLAYLIST_INDEX_ROLE, position)
            self._apply_item_flags(child)
            item.addChild(child)
            new_items.append(child)
            self._log_url_added(child, url)
        item.setExpanded(True)
        self._renumber_url_list()
        self._update_download_button()

        suffix = f", skipped {skipped} duplicate(s)" if skipped else ""
        self._append_probe_result_to_log(item, f"{title} (playlist, {len(new_items)} link(s){suffix})")
        self._on_url_list_selection_changed()
        self._probe_finished()
        self._update_refresh_button()
        for child in new_items:
            self._start_probe(child)

    # Leave the playlist link's text as-is but color the row yellow, same as a failed probe
    def _on_playlist_expand_error(self, item, message):
        self._tasks_by_item.pop(id(item), None)
        url = item.data(0, URL_ROLE) or ""
        self._set_probe_failed(item, True)
        self._save_links_to_disk()
        self._log(f"Playlist expand failed for {url}: {message}")
        self._probe_finished()

    # Queue a yt-dlp probe for an item, running on the shared probe thread pool
    # Resolve which quality tier to request for one link: its own "Force quality"
    # override if set via the context menu; failing that, its parent folder's own
    # quality override if it has one (a Sub Group channel's "Set quality..." - see
    # _set_folder_quality); failing that, the global Quality setting. Either way,
    # _format_args_for_quality() never hard-filters on resolution - it only biases
    # yt-dlp's format sort ("-S res:N"), so if the exact requested height isn't
    # available yt-dlp falls back to whichever available format has the closest
    # resolution instead of failing outright.
    def _quality_for_item(self, item):
        forced = item.data(0, FORCED_QUALITY_ROLE)
        if forced:
            return forced
        parent = item.parent()
        if parent is not None and parent.data(0, IS_FOLDER_ROLE):
            folder_quality = parent.data(0, FOLDER_QUALITY_ROLE)
            if folder_quality:
                return folder_quality
        return self.quality_combo.currentText()

    # Whether the active profile is a "Generic file" profile - i.e. its links aren't
    # videos at all, so probing/downloading them should use yt-dlp's plain file-download
    # path (see probe_url/download_url's is_file param) rather than video/audio format
    # selection.
    def _current_profile_is_generic_file(self):
        profile = self._current_profile_dict()
        return bool(profile and profile.get("type") == "Generic file")

    # Kick off a background probe for this link item, assigning it a uuid first
    # if it doesn't already have one
    def _start_probe(self, item):
        url = item.data(0, URL_ROLE)
        if not url or item.data(0, LINK_DISABLED_ROLE):
            return
        self._set_probe_failed(item, False)
        item.setData(0, MEMBERS_ONLY_ROLE, False)
        link_uuid = item.data(0, LINK_UUID_ROLE)
        if not link_uuid:
            link_uuid = str(uuid.uuid4())
            item.setData(0, LINK_UUID_ROLE, link_uuid)
        task = ProbeTask(
            item, url, link_uuid, self.probing_timeout_spin.value(),
            self._quality_for_item(item),
            self._current_proxy(),
            is_file=self._current_profile_is_generic_file(),
        )
        task.signals.finished.connect(self._on_probe_finished)
        task.signals.error.connect(self._on_probe_error)
        self._tasks_by_item[id(item)] = task
        self._probe_started()
        self._probe_pool.start(task)

    # Build a "scheme://host:port" proxy URL from the Connection settings, or None if disabled
    def _current_proxy(self):
        if not self.chk_proxy.isChecked():
            return None
        host = self.proxy_host_edit.text().strip()
        if not host:
            return None
        if not self.proxy_host_edit.hasAcceptableInput():
            self._log(f"Proxy host '{host}' is not a valid IP address, ignoring proxy")
            return None
        if "://" not in host:
            host = f"http://{host}"
        return f"{host}:{self.proxy_port_spin.value()}"

    # Rewrite a probed item's text to "<quality> <size> - <title>" once yt-dlp returns
    def _on_probe_finished(self, item, info):
        self._tasks_by_item.pop(id(item), None)
        # "quality" is "" for a "Generic file" profile's links (see probe_url) since
        # there's no video/audio format to report - leave that segment out entirely
        # rather than show a leading space or a meaningless placeholder.
        quality_prefix = f"{info['quality']} " if info["quality"] else ""
        display = f"{quality_prefix}{info['size']} - {info['title']}"
        item.setData(0, RAW_TEXT_ROLE, display)
        item.setData(0, TITLE_ROLE, info["title"])
        item.setData(0, THUMBNAIL_PATH_ROLE, info.get("thumbnail_path"))
        item.setData(0, CHANNEL_ROLE, info.get("channel"))
        item.setData(0, UPLOAD_DATE_ROLE, info.get("upload_date"))
        item.setData(0, UPLOAD_TIMESTAMP_ROLE, info.get("upload_timestamp"))
        item.setData(0, DURATION_ROLE, info.get("duration"))
        item.setData(0, SIZE_ROLE, info.get("size"))
        self._set_probe_failed(item, False)
        item.setData(0, MEMBERS_ONLY_ROLE, False)
        item.setData(0, FORCE_QUALITY_PENDING_ROLE, False)
        self._renumber_url_list()
        self._append_probe_result_to_log(item, info["title"])
        self._refresh_preview_if_current(item)
        self._probe_finished()

    # Leave the link's text as-is but color the row yellow when a probe fails, or
    # red if the failure looks like a members-only/join-to-watch video rather than
    # a generic/transient error - see MEMBERS_ONLY_ERROR_HINT.
    def _on_probe_error(self, item, message):
        self._tasks_by_item.pop(id(item), None)
        url = item.data(0, URL_ROLE) or ""
        is_members_only = MEMBERS_ONLY_ERROR_HINT in message.lower()
        self._set_probe_failed(item, True)
        item.setData(0, MEMBERS_ONLY_ROLE, is_members_only)
        item.setData(0, FORCE_QUALITY_PENDING_ROLE, False)
        self._renumber_url_list()
        if is_members_only:
            self._log(f"Probe failed for {url}: members-only video, skipping downloads - {message}")
        else:
            self._log(f"Probe failed for {url}: {message}")
        self._probe_finished()

    # Toggle the yellow failed-probe color on a row (applies to normal/hover/selected alike)
    def _set_probe_failed(self, item, failed):
        item.setData(0, PROBE_FAILED_ROLE, failed)

    # Mark one more probe/playlist task as in flight and update the sidebar status label
    def _probe_started(self):
        self._active_probe_count += 1
        self._update_status_label()

    # Mark one probe/playlist task as finished (succeeded or failed) and update the label
    def _probe_finished(self):
        self._active_probe_count = max(0, self._active_probe_count - 1)
        self._update_status_label()

    # Same idea as _probe_started/_probe_finished but for a channel/playlist
    # Refresh listing specifically - kept as a separate counter so Refresh
    # doesn't drive the Probe button's "Stop" state (they're separate actions;
    # a Channel refresh may go on to auto-probe its new links once it's done,
    # and that real probing work is what should show as "Stop" on the Probe
    # button - see _on_channel_refresh_finished / _update_status_label).
    def _refresh_task_started(self):
        self._active_refresh_count += 1
        self._update_status_label()

    def _refresh_task_finished(self):
        self._active_refresh_count = max(0, self._active_refresh_count - 1)
        self._update_status_label()

    # Show "probing" on the sidebar status label while any task is in flight, "downloading"
    # while a transfer is active, "active (waiting on scheduler)" when nothing's running but
    # the scheduler will auto-start once its start time is reached, else "ready"; also toggles
    # the Stop Probing button so it's only clickable while probing is active - except for a
    # Sub Group profile, where the same button doubles as "Start Probing" while idle, since a
    # Sub Group's Refresh deliberately leaves every new link un-probed (see
    # _on_channel_refresh_finished) rather than auto-probing them one by one.
    def _update_status_label(self):
        probing = self._active_probe_count > 0
        refreshing = self._active_refresh_count > 0
        if probing:
            state = "probing"
        elif refreshing:
            state = "refreshing"
        elif self._download_tasks:
            state = "downloading"
        elif self._download_timeouts:
            state = "ready (waiting on retry timeout)"
        elif self.chk_scheduler_start.isChecked():
            state = "active (waiting on scheduler)"
        else:
            state = "ready"
        self.status_label.setText(f"status: {state}")
        self._update_settings_sidebar_info()
        if probing:
            self.btn_stop_probing.setText("Probe")
            self.btn_stop_probing.setIcon(QIcon(_flat_icon_path("eye", TEXT_SECONDARY)))
            self.btn_stop_probing.setEnabled(True)
            self.btn_stop_probing.set_active(True)
            return
        profile = self._current_profile_dict()
        if profile and profile.get("type") == "Sub Group":
            self.btn_stop_probing.setText("Probe")
            self.btn_stop_probing.setIcon(QIcon(_flat_icon_path("eye", TEXT_SECONDARY)))
            self.btn_stop_probing.setEnabled(bool(self._unprobed_link_items()))
            self.btn_stop_probing.set_active(False)
        else:
            self.btn_stop_probing.setText("Probe")
            self.btn_stop_probing.setIcon(QIcon(_flat_icon_path("eye", TEXT_SECONDARY)))
            self.btn_stop_probing.setEnabled(False)
            self.btn_stop_probing.set_active(False)

    # Refresh the sidebar's "Profile: <name>" label and the window title's
    # "<APP_NAME> - <name>" suffix to match the active profile
    def _update_profile_label(self):
        self.profile_label.setText(f"Profile: {self._current_profile_name}")
        self.setWindowTitle(f"{APP_NAME} - {self._current_profile_name}")
        self._update_settings_sidebar_info()

    # Refresh the status/profile/quality/proxy/scheduler lines shown below the
    # separator in the shared settings sidebar. Called whenever any of the
    # underlying state changes (see _connect_signals for the wired-up signals);
    # "update:" is set separately by the yt-dlp update-check callbacks since that
    # state isn't derived from a simple widget read.
    def _update_settings_sidebar_info(self):
        if self._active_probe_count > 0:
            state = "probing"
        elif self._active_refresh_count > 0:
            state = "refreshing"
        elif self._download_tasks:
            state = "downloading"
        elif self._download_timeouts:
            state = "ready (waiting on retry timeout)"
        elif self.chk_scheduler_start.isChecked():
            state = "active (waiting on scheduler)"
        else:
            state = "ready"
        self.settings_status_label.setText(f"status: {state}")

        self.settings_profile_label.setText(f"Profile: {self._current_profile_name}")

        self.settings_quality_label.setText(
            f"profile-wide quality: {self.quality_combo.currentText()}"
        )

        if self.chk_proxy.isChecked():
            host = self.proxy_host_edit.text().strip() or "no host set"
            proxy_text = f"{host}:{self.proxy_port_spin.value()}"
        else:
            proxy_text = "off"
        self.settings_proxy_label.setText(f"proxy: {proxy_text}")

        scheduler_bits = []
        if self.chk_scheduler_start.isChecked():
            scheduler_bits.append(f"start {self.scheduler_start_time_edit.time().toString('HH:mm')}")
        if self.chk_scheduler_stop.isChecked():
            scheduler_bits.append(f"stop {self.scheduler_stop_time_edit.time().toString('HH:mm')}")
        scheduler_text = ", ".join(scheduler_bits) if scheduler_bits else "off"
        self.settings_scheduler_label.setText(f"scheduler: {scheduler_text}")

    # The Stop Probing button doubles as "Start Probing" for a Sub Group profile
    # while idle (see _update_status_label) - dispatch to whichever action the
    # button's current state/label actually represents.
    def _on_stop_probing_clicked(self):
        if self._active_probe_count > 0:
            self._stop_all_probing()
        else:
            self._start_all_probing()

    # Cancel every probe/playlist task currently in flight, killing their yt-dlp
    # processes outright rather than waiting for them to finish on their own
    def _stop_all_probing(self):
        tasks = list(self._tasks_by_item.values())
        if self._channel_refresh_task is not None:
            tasks.append(self._channel_refresh_task)
        if not tasks:
            return
        self._tasks_by_item.clear()
        self._channel_refresh_task = None
        self._subgroup_refresh_queue = []
        self._subgroup_refresh_active_channel = None
        self._playlist_refresh_queue = []
        for task in tasks:
            task.cancel()
        self._active_probe_count = 0
        self._active_refresh_count = 0
        self._update_status_label()
        self._update_refresh_button()
        self._log(f"Stopped {len(tasks)} in-progress probe(s)")

    # Links in the active profile with no recorded title (i.e. never successfully
    # probed, including ones whose last probe failed) that aren't disabled,
    # members-only, or already probing right now - what "Start Probing" targets.
    def _unprobed_link_items(self):
        return [
            item for item in self._iter_all_link_items()
            if item.data(0, URL_ROLE)
            and not item.data(0, LINK_DISABLED_ROLE)
            and not item.data(0, MEMBERS_ONLY_ROLE)
            and not item.data(0, TITLE_ROLE)
            and id(item) not in self._tasks_by_item
        ]

    # "Start Probing": queue a probe for every not-yet-probed link in the tree at
    # once. Exists mainly for a Sub Group profile, whose Refresh deliberately skips
    # auto-probing each new link as it's appended (see _on_channel_refresh_finished)
    # to keep the channel-to-channel refresh queue moving without waiting on the
    # probe pool - this is the bulk catch-up for all those links, without needing to
    # select them all and use "Retry probe" from the context menu by hand.
    def _start_all_probing(self):
        items = self._unprobed_link_items()
        if not items:
            self._log("Probe: no un-probed link(s) to probe")
            return
        for item in items:
            self._start_probe(item)
        self._log(f"Probing {len(items)} link(s)")

    # Download button toggles between starting downloads and stopping every download
    # currently in flight, depending on whether any are running right now
    def _on_download_button_clicked(self):
        if self._download_tasks or self._download_timeouts:
            self._stop_all_downloads()
        else:
            self._start_downloads()

    # Cancel every download currently in flight (killing their yt-dlp processes
    # outright rather than waiting for them to finish on their own), and cancel any
    # link still sitting out a retry cooldown too, so "Stop Downloads" reliably
    # halts everything the button implies is running.
    def _stop_all_downloads(self):
        tasks = list(self._download_tasks.values())
        timeouts = list(self._download_timeouts.values())
        if not tasks and not timeouts:
            return
        for task in tasks:
            self._note_download_batch_result(task.item, success=False, message="stopped by user")
        self._download_tasks.clear()
        for task in tasks:
            task.cancel()
        for info in timeouts:
            info["item"].setData(0, DOWNLOAD_TIMEOUT_ROLE, None)
        self._download_timeouts.clear()
        self._download_timeout_timer.stop()
        if timeouts:
            self._refresh_url_list_display()
        self._update_download_button()
        self._update_status_label()
        parts = []
        if tasks:
            parts.append(f"{len(tasks)} in-progress download(s)")
        if timeouts:
            parts.append(f"{len(timeouts)} pending retry(ies)")
        self._log("Stopped " + " and ".join(parts))
        self._maybe_log_download_batch_summary()

    # Label the Download button "Stop Downloads" while any are running or waiting
    # out a retry cooldown, else "Download"; when idle, grey it out if there's
    # nothing enabled left to download (or the list is empty) so it doesn't look
    # actionable when it isn't
    def _update_download_button(self):
        downloading = bool(self._download_tasks) or bool(self._download_timeouts)
        self.btn_download.setText("Download")
        self.btn_download.setIcon(QIcon(_flat_icon_path("download", TEXT_SECONDARY)))
        self.btn_download.set_active(downloading)
        has_enabled_link = any(
            not item.data(0, LINK_DISABLED_ROLE)
            and not item.data(0, MEMBERS_ONLY_ROLE)
            and not item.data(0, LINK_SKIPPED_ROLE)
            and item.data(0, TITLE_ROLE)
            and item.data(0, DOWNLOAD_PROGRESS_ROLE) != 100
            for item in self._iter_all_link_items()
        )
        self.btn_download.setEnabled(downloading or has_enabled_link)

    # Fill any free download slots (up to the "Parallel downloads" limit) by scanning
    # the tree top-to-bottom for the first not-disabled, not-yet-downloaded link(s).
    # Acts as a continuous queue: _on_download_finished/_on_download_error call this
    # again (quietly) whenever a slot frees up, so downloading keeps working through
    # the list on its own - including links enabled after downloading was started -
    # without needing another press of the Download button.
    # A link's download destination is the configured location, unless it sits
    # inside a folder in the tree - in that case it goes into a same-named
    # subfolder of the location (created on demand). Applies to every profile:
    # a Channel's auto-created folder, a converted Playlist folder, or any
    # folder the user made by hand via "Move to folder" all work the same way.
    def _download_dest_dir_for_folder(self, folder_name, location):
        if not folder_name:
            return location
        dest = Path(location) / _sanitize_profile_name(folder_name)
        try:
            dest.mkdir(parents=True, exist_ok=True)
        except OSError:
            return location
        return str(dest)

    # A Sub Group profile keeps each of its channels in its own top-level folder in
    # the sidebar (so they're easy to tell apart and each has its own refresh
    # tracking), but downloads from every channel land in one shared folder named
    # after the Sub Group itself, not split back out per channel. This maps a
    # top-level folder name over to that shared name when it's one of the active
    # Sub Group's channels; any other folder (a plain Channel/Playlist folder, or a
    # folder the user made by hand) is returned unchanged.
    def _effective_download_folder_name(self, folder_name):
        profile = self._current_profile_dict()
        if profile and profile.get("type") == "Sub Group":
            channel_names = {c.get("name") for c in (profile.get("channels") or [])}
            if folder_name in channel_names:
                return profile.get("name")
        return folder_name

    # Resolve the folder a given link item's download should land in
    def _download_dest_dir_for_item(self, item, location):
        parent = item.parent()
        if parent is not None and parent.data(0, IS_FOLDER_ROLE):
            folder_name = self._effective_download_folder_name(parent.data(0, RAW_TEXT_ROLE))
            return self._download_dest_dir_for_folder(folder_name, location)
        return location

    # Start as many queued downloads as the parallel-downloads limit still allows
    def _start_downloads(self, quiet=False):
        limit = self.parallel_downloads_spin.value()
        location = self.location_edit.text().strip()
        if not location:
            if not quiet:
                self._log("Download: no download location is set")
            return
        available_slots = limit - len(self._download_tasks)
        if available_slots <= 0:
            if not quiet:
                self._log(f"Download: already running {len(self._download_tasks)} download(s) (limit {limit})")
            return
        started = 0
        for item in self._download_fill_order():
            if started >= available_slots:
                break
            if item.data(0, LINK_DISABLED_ROLE):
                continue
            if item.data(0, MEMBERS_ONLY_ROLE):
                continue
            if item.data(0, LINK_SKIPPED_ROLE):
                continue
            if id(item) in self._download_tasks:
                continue
            if id(item) in self._download_timeouts:
                continue
            if item.data(0, DOWNLOAD_PROGRESS_ROLE) == 100:
                continue
            if not item.data(0, URL_ROLE):
                continue
            dest = self._download_dest_dir_for_item(item, location)
            self._start_download(item, dest)
            started += 1
        if started == 0 and not quiet:
            self._log("Download: no link(s) available to download")
        self._maybe_log_download_batch_summary()

    # The order _start_downloads fills free slots from: normally just every link in
    # tree top-to-bottom order (_iter_all_link_items), same as always. But for a Sub
    # Group with "Number downloads by upload order" on, that tree order is exactly
    # what we need to ignore - a Refresh can freely reshuffle which channel folder
    # ends up first without affecting which video downloads first. Sort by the same
    # precomputed upload-order rank used for numbering instead (see
    # _subgroup_upload_order_map), so the oldest not-yet-downloaded upload across
    # every channel in the group always gets first crack at a free slot.
    def _download_fill_order(self):
        order_map = self._subgroup_upload_order_map()
        items = list(self._iter_all_link_items())
        if order_map is not None:
            items.sort(key=lambda it: order_map.get(id(it), len(order_map) + 1))
        return items

    # Ticks once a second: fires the scheduler's start/stop times (each at most
    # once per calendar day), and also drives the periodic About-tab version
    # refresh below (piggybacking on this tick instead of a second QTimer).
    def _on_scheduler_tick(self):
        now = time.localtime()
        now_hm = (now.tm_hour, now.tm_min)
        today = time.strftime("%Y-%m-%d", now)

        if self.chk_scheduler_start.isChecked() and not self._download_tasks \
                and self._scheduler_last_start_day != today:
            t = self.scheduler_start_time_edit.time()
            if (t.hour(), t.minute()) == now_hm:
                self._scheduler_last_start_day = today
                self._scheduler_start_run()

        if self.chk_scheduler_stop.isChecked() and self._download_tasks \
                and self._scheduler_last_stop_day != today:
            t = self.scheduler_stop_time_edit.time()
            if (t.hour(), t.minute()) == now_hm:
                self._scheduler_last_stop_day = today
                self._scheduler_stop_run("scheduled stop time reached")

        # Re-run the app/yt-dlp/ffmpeg version checks every 6 hours the app stays
        # open (they already run once at startup - see __init__), so the About
        # tab doesn't go stale on a long-running instance.
        self._version_refresh_tick_counter += 1
        if self._version_refresh_tick_counter >= 6 * 3600:
            self._version_refresh_tick_counter = 0
            self._start_ytdlp_update_check()
            self._start_ffmpeg_update_check()
            self._start_app_update_check()

    # Scheduler-triggered equivalent of clicking "Download"
    def _scheduler_start_run(self):
        self._log("Scheduler: automatic start time reached")
        self._start_downloads()

    # Scheduler-triggered equivalent of clicking "Stop Downloads"
    def _scheduler_stop_run(self, reason):
        self._log(f"Scheduler: stopping downloads ({reason})")
        self._stop_all_downloads()

    # The "Ignore pattern in title" setting only applies to videos that came from a
    # standalone Channel or Playlist profile - i.e. items living inside a folder -
    # not standalone single-video links (whose title the user picked/accepted
    # individually), and not a Sub Group (see _update_ignore_title_pattern_visibility
    # for why). Returns None if the setting's blank, the item isn't inside a folder,
    # the profile isn't a Channel/Playlist, or the regex the user typed doesn't
    # actually compile (logged once here rather than letting a bad pattern silently
    # break every download in the batch).
    def _ignore_title_pattern_for_item(self, item):
        parent = item.parent()
        if parent is None or not parent.data(0, IS_FOLDER_ROLE):
            return None
        profile = self._current_profile_dict()
        if not profile or profile.get("type") not in ("Channel", "Playlist"):
            return None
        pattern = self.ignore_title_pattern_edit.text().strip()
        if not pattern:
            return None
        try:
            re.compile(pattern)
        except re.error as exc:
            self._log(f"Ignore pattern in title is not a valid regex, ignoring it: {exc}")
            return None
        return pattern

    # Log "Downloading: <name>" and reserve an empty line immediately below it -
    # tracked the same way _on_download_line tracks any other item's progress line -
    # so the first progress update lands directly under its own "Downloading:" line
    # (styled as "|__ 52.8% of ...") rather than at the end of the log, wherever
    # that happens to be once other downloads have logged things in between. Also
    # remembers this line's own block number (see _mark_download_log_line_complete).
    def _log_download_started(self, item):
        name = item.data(0, TITLE_ROLE) or item.data(0, URL_ROLE) or ""
        self._log(f"Downloading: {name}")
        self._download_start_blocks[id(item)] = self.log.document().lastBlock().blockNumber()
        cursor = QTextCursor(self.log.document().lastBlock())
        cursor.movePosition(QTextCursor.MoveOperation.EndOfBlock)
        cursor.insertBlock()
        self._download_line_blocks[id(item)] = self.log.document().lastBlock().blockNumber()

    # Which number (if any) to hardcode onto this download's filename as a
    # "<n> - title.ext" prefix (see download_url's name_template). A Sub Group with
    # "Number downloads by upload order" on always wins here and uses that global
    # oldest-first rank, regardless of the "Number playlist downloads" setting
    # (which doesn't apply to Sub Group profiles at all - see
    # _update_number_playlist_downloads_visibility). Otherwise, falls back to the
    # normal playlist-position numbering, if enabled.
    def _download_number_for_item(self, item):
        order_map = self._subgroup_upload_order_map()
        if order_map is not None:
            return order_map.get(id(item))
        if not self.chk_number_playlist_downloads.isChecked():
            return None
        return item.data(0, PLAYLIST_INDEX_ROLE)

    # Kick off one DownloadTask for the given link item on the shared download pool
    def _start_download(self, item, location):
        self._note_download_batch_start(item)
        self._log_download_started(item)
        task = DownloadTask(
            item, item.data(0, URL_ROLE), location,
            self._quality_for_item(item), self.retry_count_spin.value(),
            self._current_proxy(),
            playlist_index=self._download_number_for_item(item),
            ignore_title_pattern=self._ignore_title_pattern_for_item(item),
            is_file=self._current_profile_is_generic_file(),
        )
        task.signals.progress.connect(self._on_download_progress)
        task.signals.speed.connect(self._on_download_speed)
        task.signals.line.connect(self._on_download_line)
        task.signals.finished.connect(self._on_download_finished)
        task.signals.error.connect(self._on_download_error)
        self._download_tasks[id(item)] = task
        self._download_pool.start(task)
        self._update_download_button()
        self._update_status_label()

    # Update a link's persisted download percentage and refresh its displayed text
    def _set_download_progress(self, item, percent):
        item.setData(0, DOWNLOAD_PROGRESS_ROLE, percent)
        self._renumber_url_list()

    def _on_download_progress(self, item, percent):
        # A progress update means this attempt actually started transferring bytes,
        # so whatever consecutive-failure streak it was on is no longer relevant.
        self._download_retry_counts.pop(id(item), None)
        self._set_download_progress(item, percent)

    # Relay a live speed reading to the item's row
    def _on_download_speed(self, item, kbps):
        link_uuid = item.data(0, LINK_UUID_ROLE)
        if link_uuid:
            self.set_download_speed(link_uuid, kbps)

    # Handle a download that finished without error, verifying it actually
    # produced a real file before marking the row complete
    def _on_download_finished(self, item, final_path):
        self._download_tasks.pop(id(item), None)
        self._remove_download_log_line(item)
        link_uuid = item.data(0, LINK_UUID_ROLE)
        # yt-dlp can exit 0 (a "successful" run, so DownloadTask emitted "finished"
        # rather than "error") without ever having reported a real output file - e.g.
        # no line matched _DOWNLOAD_DESTINATION_RE/_DOWNLOAD_ALREADY_DONE_RE, or it did
        # match but the reported path doesn't actually exist on disk (a postprocessing
        # step renamed/removed it after logging that line, or the match was against an
        # intermediate fragment that never got merged into the real final file). Treat
        # that the same as a failed attempt instead of unconditionally painting the row
        # green/100% over a download that never actually produced anything - otherwise
        # the link is left looking "Completed" forever with no file behind it.
        if final_path and not Path(final_path).is_file():
            final_path = None
        if not final_path:
            self._download_start_blocks.pop(id(item), None)
            if link_uuid:
                self.set_download_speed(link_uuid, 0)
            message = "yt-dlp reported success but no output file was found"
            self._log(f"❌ Download failed for {item.data(0, URL_ROLE) or ''}: {message}")
            self._note_download_batch_result(item, success=False, message=message)
            self._register_download_failure(item)
            self._update_download_button()
            self._update_status_label()
            self._start_downloads(quiet=True)
            return
        if link_uuid:
            self.set_download_speed(link_uuid, 0)
        self._set_download_progress(item, 100)
        self._update_sidebar_info()
        final_path = self._relocate_to_current_folder(item, final_path)
        final_path = self._dedupe_download_filename(item, final_path)
        item.setData(0, DOWNLOAD_PATH_ROLE, final_path)
        self._save_links_to_disk()
        name = item.data(0, TITLE_ROLE) or item.data(0, URL_ROLE) or ""
        self._mark_download_log_line_complete(item, name)
        self._note_download_batch_result(item, success=True)
        self._update_download_button()
        self._update_status_label()
        self._start_downloads(quiet=True)

    # Strip the " [id]" uniqueness tag yt-dlp's output template added (see
    # download_url) back off a just-finished download, giving it the clean name the
    # user actually wants - "name.webm". If another *different* video already holds
    # that clean name (a genuine title collision), fall back to "name_1.webm",
    # "name_2.webm", and so on until a free one turns up, same as the uploader's own
    # numbering would. A file already sitting at the clean name is only ever treated
    # as "not a collision" when it's this exact item's own previously recorded
    # download (e.g. redownloading after Reset) - then it's replaced outright rather
    # than needlessly piling up a fresh _1/_2/... copy of the same video.
    def _dedupe_download_filename(self, item, final_path):
        path = Path(final_path)
        if not path.exists():
            return final_path
        match = _ID_TAG_RE.match(path.stem)
        desired_stem = match.group(1) if match else path.stem
        own_previous_path = item.data(0, DOWNLOAD_PATH_ROLE)
        candidate = path.with_name(f"{desired_stem}{path.suffix}")
        suffix_num = 1
        while candidate != path and candidate.exists():
            if str(candidate) == own_previous_path:
                if not self._retry_fs_op(candidate.unlink):
                    self._log(
                        f"Couldn't replace previous file for {item.data(0, URL_ROLE) or ''} "
                        "(file may be open elsewhere) - keeping the freshly downloaded "
                        f"copy as {path.name}"
                    )
                    return final_path
                break
            candidate = path.with_name(f"{desired_stem}_{suffix_num}{path.suffix}")
            suffix_num += 1
        if candidate == path:
            return final_path
        if not self._retry_fs_op(lambda: path.rename(candidate)):
            self._log(
                f"Couldn't rename downloaded file for {item.data(0, URL_ROLE) or ''} "
                f"(file may be open elsewhere) - it's saved on disk as {path.name}"
            )
            return final_path
        return str(candidate)

    # Retries a filesystem operation a few times with a short delay, to ride out a
    # file being *briefly* locked by something else right after yt-dlp closes it -
    # Windows Defender's real-time scan and search indexers are common culprits.
    # Returns True on success, False if it still failed after every attempt (the
    # caller decides what to do then - it's not treated as fatal).
    @staticmethod
    # Retry a filesystem operation a few times before giving up, since a file can
    # briefly be locked by another process (e.g. antivirus, indexing)
    def _retry_fs_op(op, attempts=5, delay=0.3):
        for attempt in range(attempts):
            try:
                op()
                return True
            except OSError:
                if attempt == attempts - 1:
                    return False
                time.sleep(delay)
        return False

    # A download's destination directory is fixed the moment its DownloadTask starts,
    # so if the item gets dragged into a (different) folder while that download is
    # still in flight, the finished file lands wherever the task started writing it -
    # not wherever the item now lives in the tree. Called right as a download finishes,
    # this moves the file to match the item's *current* parent folder if the two have
    # drifted apart, so a mid-download move behaves the same as moving an already-
    # completed (or not-yet-started) link: the on-disk location always follows the tree,
    # regardless of what state the link was in (downloading/completed/errored) when moved.
    def _relocate_to_current_folder(self, item, final_path):
        location = self.location_edit.text().strip()
        if not location:
            return final_path
        expected_dir = Path(self._download_dest_dir_for_item(item, location))
        current_path = Path(final_path)
        if current_path.parent == expected_dir:
            return final_path
        new_path = expected_dir / current_path.name
        try:
            expected_dir.mkdir(parents=True, exist_ok=True)
            if not current_path.is_file():
                return final_path
            shutil.move(str(current_path), str(new_path))
        except OSError as exc:
            self._log(f"Couldn't move downloaded file for {item.data(0, URL_ROLE) or ''}: {exc}")
            return final_path
        self._log(f"Moved downloaded file to {expected_dir}")
        return str(new_path)

    # Handle a failed download attempt: clean up its row/log state and queue a
    # retry if attempts remain
    def _on_download_error(self, item, message):
        self._download_tasks.pop(id(item), None)
        self._remove_download_log_line(item)
        self._download_start_blocks.pop(id(item), None)
        # yt-dlp can report a 100% progress line for the raw transfer and still fail
        # afterward (e.g. the ffmpeg merge step, or post-processing) - _on_download_progress
        # already stamped DOWNLOAD_PROGRESS_ROLE == 100 on this row when that line came in,
        # which paints it green as "complete". Clear it back out here so a later failure
        # doesn't leave a never-finished download looking done.
        item.setData(0, DOWNLOAD_PROGRESS_ROLE, None)
        link_uuid = item.data(0, LINK_UUID_ROLE)
        if link_uuid:
            self.set_download_speed(link_uuid, 0)
        self._note_download_batch_result(item, success=False, message=message)
        # Don't log this attempt as a "failed" download yet - _register_download_failure
        # only logs (and cools down) once retries are actually exhausted. A single
        # attempt tripped up by an unstable connection that the queue silently retries
        # and finishes moments later isn't a real failure, just noise.
        self._register_download_failure(item)
        self._update_download_button()
        self._update_status_label()
        self._start_downloads(quiet=True)

    # Count a failed download attempt against the link's retry limit. Once the limit
    # is reached, put the link on a retry cooldown instead of letting _start_downloads
    # pick it straight back up and log it as an actual failure; otherwise just let the
    # existing queue naturally retry it (_start_downloads is already re-invoked right
    # after this by the caller) without logging anything - a hiccup that resolves on
    # its own doesn't count as a failure.
    def _register_download_failure(self, item):
        key = id(item)
        limit = self.download_retry_limit_spin.value()
        attempts = self._download_retry_counts.get(key, 0) + 1
        if attempts >= limit:
            self._download_retry_counts.pop(key, None)
            cooldown = self.download_retry_cooldown_spin.value()
            self._begin_download_timeout(item, cooldown)
            self._log(
                f"❌ Download failed {attempts} time(s) in a row, cooling down for "
                f"{cooldown}s: {item.data(0, URL_ROLE) or ''}"
            )
        else:
            self._download_retry_counts[key] = attempts

    # Marks the current download run as active and adds this link to it the first
    # time it starts downloading, so the end-of-run summary (see
    # _maybe_log_download_batch_summary) knows to include it. A link that's started
    # more than once in the same run (e.g. retried after a failure) is only added
    # once here - _note_download_batch_result keeps its entry up to date afterward.
    def _note_download_batch_start(self, item):
        self._download_batch_active = True
        self._download_batch_items.setdefault(
            id(item), {"item": item, "success": False, "message": None}
        )

    # Records this link's outcome for the current download run - overwriting any
    # earlier outcome for the same link, so a failure that's later retried
    # successfully is reported as a success, and a link that fails again after an
    # earlier success (shouldn't normally happen, but just in case) is reported as
    # its most recent outcome instead of stacking up duplicate entries.
    def _note_download_batch_result(self, item, success, message=None):
        entry = self._download_batch_items.get(id(item))
        if entry is None:
            return
        entry["success"] = success
        entry["message"] = message

    # Once the download run genuinely has nothing left in flight or waiting on a
    # retry cooldown, log a "====" summary of everything that run touched - how many
    # links finished successfully and, only if any did, how many failed and which
    # ones (with each one's last failure reason). Called after every attempt to fill
    # download slots and whenever downloads are stopped outright, so the summary
    # fires whether the run finishes naturally or is cut short by the user/scheduler.
    def _maybe_log_download_batch_summary(self):
        if not self._download_batch_active:
            return
        if self._download_tasks or self._download_timeouts:
            return
        items = list(self._download_batch_items.values())
        self._download_batch_active = False
        self._download_batch_items = {}
        if not items:
            return
        successes = [entry for entry in items if entry["success"]]
        failures = [entry for entry in items if not entry["success"]]
        self._log("=" * 13)
        self._log(f"Completed {len(successes)} download(s)")
        if failures:
            self._log(f"❌ Failed {len(failures)} download(s)")
            for entry in failures:
                item = entry["item"]
                name = item.data(0, TITLE_ROLE) or item.data(0, URL_ROLE) or ""
                reason = f": {entry['message']}" if entry["message"] else ""
                self._log(f"❌ Failed {name}{reason}")
        self._log("=" * 13)

    # Put a link on a retry cooldown for the given number of seconds: exclude it from
    # _start_downloads, show the "[Ns] - " countdown prefix in yellow, and make sure
    # the per-second tick timer is running to count it down.
    def _begin_download_timeout(self, item, seconds):
        self._download_timeouts[id(item)] = {"item": item, "remaining": seconds}
        item.setData(0, DOWNLOAD_TIMEOUT_ROLE, seconds)
        self._renumber_url_list()
        if not self._download_timeout_timer.isActive():
            self._download_timeout_timer.start()

    # Count every active retry cooldown down by one second, refresh the row text/
    # colors, and resume downloading any link whose cooldown just finished
    def _on_download_timeout_tick(self):
        expired = []
        for key, info in self._download_timeouts.items():
            info["remaining"] -= 1
            item = info["item"]
            if info["remaining"] <= 0:
                expired.append(key)
            else:
                item.setData(0, DOWNLOAD_TIMEOUT_ROLE, info["remaining"])
        for key in expired:
            info = self._download_timeouts.pop(key)
            item = info["item"]
            item.setData(0, DOWNLOAD_TIMEOUT_ROLE, None)
            self._log(f"Retry cooldown finished: {item.data(0, URL_ROLE) or ''}")
        self._refresh_url_list_display()
        if not self._download_timeouts:
            self._download_timeout_timer.stop()
        if expired:
            self._start_downloads(quiet=True)
            self._update_status_label()

    # Refresh the sidebar preview (thumbnail/title/subtitle/detail) to match the current selection
    def _on_url_list_selection_changed(self):
        selected = self.url_list.selectedItems()
        if len(selected) == 1 and selected[0].data(0, IS_FOLDER_ROLE):
            self._show_folder_preview(selected[0])
            return
        items = [it for it in selected if not it.data(0, IS_FOLDER_ROLE)]
        if len(items) != 1:
            self._clear_preview()
            return
        self._show_preview(items[0])

    # Acts as the "button" for a "Load more" sentinel row; no-op for any other row.
    # Materializing a batch (up to LINKS_LOAD_BATCH_SIZE, i.e. "Load 500 more...")
    # builds that many real QTreeWidgetItems synchronously, which can take long enough
    # on a large list to be noticeable, so show a busy cursor for the duration.
    def _on_url_list_item_clicked(self, item, column):
        if item.data(0, IS_LOAD_MORE_ROLE):
            QApplication.setOverrideCursor(Qt.WaitCursor)
            QApplication.processEvents()
            try:
                self._expand_load_more(item)
            finally:
                QApplication.restoreOverrideCursor()

    # Launch a fully-downloaded link's video file in the system default media
    # player on double-click. No-op for folders, incomplete/never-downloaded
    # links, or files whose extension isn't a recognized video type.
    def _on_url_list_item_double_clicked(self, item, column):
        if item.data(0, IS_FOLDER_ROLE):
            return
        if item.data(0, DOWNLOAD_PROGRESS_ROLE) != 100:
            return
        path_str = item.data(0, DOWNLOAD_PATH_ROLE)
        if not path_str:
            return
        path = Path(path_str)
        if path.suffix.lower() not in VIDEO_FILE_EXTENSIONS:
            return
        if not path.exists():
            self._log(f"Cannot open, file not found: {path}")
            return
        QDesktopServices.openUrl(QUrl.fromLocalFile(str(path)))

    # Reset the preview box to its empty "No preview" state
    def _clear_preview(self):
        self.preview_label.setPixmap(QPixmap())
        self.preview_label.setText("No preview")
        self.title_label.setText("")
        self.title_label.setToolTip("")
        self.title_label.setVisible(False)
        self.subtitle_label.setText("")
        self.subtitle_label.setToolTip("")
        self.subtitle_label.setVisible(False)
        self.detail_label.setText("")
        self.detail_label.setToolTip("")
        self.detail_label.setVisible(False)
        self.duration_label.setText("")
        self.duration_label.setVisible(False)

    # Set a label's text elided with "..." if it's too wide to fit, instead of letting the
    # sidebar grow and become horizontally scrollable. Full text is kept as a tooltip.
    def _set_elided_text(self, label, text, max_width=260):
        elided = label.fontMetrics().elidedText(text, Qt.TextElideMode.ElideRight, max_width)
        label.setText(elided)
        label.setToolTip(text if elided != text else "")
        # Hidden rather than just left blank when there's nothing to show, so an
        # empty title/subtitle/detail line doesn't leave dead space under the
        # thumbnail (same reasoning as duration_label below)
        label.setVisible(bool(text))

    # Populate the preview box (thumbnail image + title/url/quality) for one selected link
    def _show_preview(self, item):
        thumb_path = item.data(0, THUMBNAIL_PATH_ROLE)
        pixmap = QPixmap(thumb_path) if thumb_path else QPixmap()
        if not pixmap.isNull():
            scaled = pixmap.scaled(
                self.preview_label.width(), self.preview_label.height(),
                Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation,
            )
            self.preview_label.setPixmap(scaled)
            self.preview_label.setText("")
        else:
            self.preview_label.setPixmap(QPixmap())
            self.preview_label.setText("No preview")

        url = item.data(0, URL_ROLE) or ""
        raw = item.data(0, RAW_TEXT_ROLE) or url
        # Not yet probed: raw text is still just the URL, so there's nothing
        # meaningful to show yet — leave title/subtitle/detail blank rather
        # than displaying the raw link.
        if raw == url:
            self._set_elided_text(self.title_label, "")
            self._set_elided_text(self.subtitle_label, "")
            self._set_elided_text(self.detail_label, "")
            self.duration_label.setText("")
            self.duration_label.setVisible(False)
            return
        # Once probed, raw text is "<quality> <size> - <title>"
        if " - " in raw:
            quality_size, title = raw.split(" - ", 1)
        else:
            quality_size, title = "", raw
        channel = item.data(0, CHANNEL_ROLE) or ""
        upload_date = item.data(0, UPLOAD_DATE_ROLE) or ""
        size = item.data(0, SIZE_ROLE) or ""
        duration = item.data(0, DURATION_ROLE) or ""
        # "2024.06.23 - 32mb" once both are known; before probing (or if either is
        # missing) fall back to whatever we had before (URL / quality+size)
        date_size = " - ".join(part for part in (upload_date, size) if part)
        self._set_elided_text(self.title_label, title)
        self._set_elided_text(self.subtitle_label, channel or url)
        self._set_elided_text(self.detail_label, date_size or quality_size)
        # Only shown when yt-dlp actually reported a duration (e.g. hidden for
        # livestreams), rather than displaying an empty/misleading "0:00"
        self.duration_label.setText(duration)
        self.duration_label.setVisible(bool(duration))

    # Refresh the preview box in place if the item currently shown is the one that just probed
    def _refresh_preview_if_current(self, item):
        selected = self.url_list.selectedItems()
        if len(selected) == 1 and selected[0] is item:
            self._show_preview(item)

    # Populate the preview box for one selected folder: no thumbnail (folders don't
    # have one), just its name and the quality currently applied to it - its own
    # per-channel override (Sub Group channel, set via "Set quality...") if it has
    # one, otherwise the global Quality setting it's inheriting.
    def _show_folder_preview(self, folder_item):
        self.preview_label.setPixmap(QPixmap())
        self.preview_label.setText("No preview")
        name = folder_item.data(0, RAW_TEXT_ROLE) or ""
        quality = folder_item.data(0, FOLDER_QUALITY_ROLE) or self.quality_combo.currentText()
        self._set_elided_text(self.title_label, name)
        self._set_elided_text(self.subtitle_label, f"Quality: {quality}")
        self._set_elided_text(self.detail_label, "")
        self.duration_label.setText("")
        self.duration_label.setVisible(False)

    # Context menu for right-clicking empty space in the tree (no link/folder under
    # the cursor): just Search, plus Expand all folders (if the tree has any folder)
    # and, for a Sub Group profile, Reset numbering.
    def _show_url_list_background_menu(self, pos):
        menu = QMenu(self)
        menu.setStyleSheet(menu_style())
        act_search = menu.addAction("Search")
        menu.addSeparator()
        has_any_folder = self._has_any_folder()
        act_expand_all = menu.addAction("Expand all folders") if has_any_folder else None
        act_collapse_all = menu.addAction("Collapse all folders") if has_any_folder else None
        if has_any_folder:
            menu.addSeparator()
        profile = self._current_profile_dict()
        is_subgroup = bool(profile and profile.get("type") == "Sub Group")
        is_channel_or_subgroup = bool(profile and profile.get("type") in ("Channel", "Sub Group"))
        act_reset_numbering = menu.addAction("Reset numbering") if is_subgroup else None
        act_show_completed = menu.addAction("Show completed") if is_channel_or_subgroup else None
        menu.addSeparator()
        act_toggle_hide_skipped = menu.addAction(
            "Show skipped" if self._hide_skipped_links else "Hide skipped"
        )
        action = menu.exec(self.url_list.viewport().mapToGlobal(pos))
        if action == act_search:
            self._show_search_dialog()
        elif act_expand_all is not None and action == act_expand_all:
            self._expand_all_folders()
        elif act_collapse_all is not None and action == act_collapse_all:
            self._collapse_all_folders()
        elif act_reset_numbering is not None and action == act_reset_numbering:
            self._reset_subgroup_numbering()
        elif act_show_completed is not None and action == act_show_completed:
            self._show_completed_links_dialog()
        elif action == act_toggle_hide_skipped:
            self._hide_skipped_links = not self._hide_skipped_links
            self._refresh_skip_visibility()

    # Expand every folder in the tree, recursively - "Expand all folders" in the
    # background context menu.
    def _expand_all_folders(self):
        # Recursively expand every folder under parent
        def expand(parent):
            count = (
                self.url_list.topLevelItemCount() if parent is None else parent.childCount()
            )
            for i in range(count):
                child = self.url_list.topLevelItem(i) if parent is None else parent.child(i)
                if child.data(0, IS_FOLDER_ROLE):
                    child.setExpanded(True)
                    expand(child)

        expand(None)

    # Collapse every folder in the tree, recursively - "Collapse all folders" in
    # the background and folder context menus.
    def _collapse_all_folders(self):
        # Recursively collapse every folder under parent
        def collapse(parent):
            count = (
                self.url_list.topLevelItemCount() if parent is None else parent.childCount()
            )
            for i in range(count):
                child = self.url_list.topLevelItem(i) if parent is None else parent.child(i)
                if child.data(0, IS_FOLDER_ROLE):
                    collapse(child)
                    child.setExpanded(False)

        collapse(None)

    # Whether the tree currently contains at least one folder - governs when
    # "Expand/Collapse all folders" is offered in a context menu.
    def _has_any_folder(self):
        return any(
            self.url_list.topLevelItem(i).data(0, IS_FOLDER_ROLE)
            for i in range(self.url_list.topLevelItemCount())
        )

    # Apply the current "Hide skipped" toggle to every link in the tree: hides
    # (or reveals) each skipped link via setHidden() without touching its data,
    # so toggling "Show skipped" back on instantly recovers every hidden link
    # exactly as it was. Called whenever the toggle flips, and whenever a link's
    # skipped state changes, so newly-skipped/unskipped links stay in sync.
    def _refresh_skip_visibility(self):
        for item in self._iter_all_link_items():
            item.setHidden(self._hide_skipped_links and bool(item.data(0, LINK_SKIPPED_ROLE)))

    # "Reset numbering" (Sub Group background context menu): freeze every currently
    # -completed link out of the numbering sequence for good, the same treatment a
    # skipped link already gets (see LINK_NUMBERING_RESET_ROLE, _renumber_siblings,
    # _subgroup_upload_order_map), so whatever hasn't downloaded yet renumbers down
    # to start at 1 again and the next file written to disk is numbered 1.
    def _reset_subgroup_numbering(self):
        count = 0
        for item in self._iter_all_link_items():
            if item.data(0, DOWNLOAD_PROGRESS_ROLE) == 100 and not item.data(0, LINK_NUMBERING_RESET_ROLE):
                item.setData(0, LINK_NUMBERING_RESET_ROLE, True)
                count += 1
        self._renumber_url_list()
        self._log(f"Reset numbering: {count} completed link(s) will no longer be numbered")

    # "Show completed" (Channel/Sub Group background context menu): lists every
    # completed link in the profile, with an option to bulk-remove all of them
    # except whichever are the most recent - i.e. the tracking anchor(s) a future
    # "Refresh" treats as already-caught-up (see _most_recent_channel_link_ids) -
    # so cleaning up old completed downloads never accidentally removes the exact
    # video(s) an upload check would otherwise re-add as "new".
    def _show_completed_links_dialog(self):
        dialog = QDialog(self)
        dialog.setWindowTitle("Completed links")
        dialog.setMinimumWidth(420)
        dialog.setMinimumHeight(320)
        layout = QVBoxLayout(dialog)

        list_widget = QListWidget()
        list_widget.setStyleSheet(profile_list_style())
        layout.addWidget(list_widget, stretch=1)

        status_label = QLabel("")
        status_label.setStyleSheet(sidebar_label_muted_style())
        layout.addWidget(status_label)

        row = QHBoxLayout()
        btn_remove = QPushButton("Remove all except most recent")
        btn_remove.setStyleSheet(button_style())
        btn_close = QPushButton("Close")
        btn_close.setStyleSheet(button_style())
        row.addWidget(btn_remove)
        row.addStretch()
        row.addWidget(btn_close)
        layout.addLayout(row)

        removable_items = []

        # Rebuild the completed-links list shown in the dialog
        def refresh():
            nonlocal removable_items
            list_widget.clear()
            completed = [
                it for it in self._iter_all_link_items()
                if it.data(0, DOWNLOAD_PROGRESS_ROLE) == 100
            ]
            most_recent_ids = self._most_recent_channel_link_ids()
            removable_items = [it for it in completed if id(it) not in most_recent_ids]
            removable_ids = {id(it) for it in removable_items}
            for it in completed:
                date = _format_upload_date(it.data(0, UPLOAD_DATE_ROLE) or "")
                label = it.data(0, RAW_TEXT_ROLE) or it.text(0)
                text = f"{label}{f'  -  {date}' if date else ''}"
                if id(it) not in removable_ids:
                    text += "  (most recent)"
                list_widget.addItem(text)
            status_label.setText(
                f"{len(completed)} completed link(s), {len(removable_items)} removable"
            )
            btn_remove.setEnabled(bool(removable_items))

        # Delete the removable completed links, then refresh the list
        def on_remove_clicked():
            if not removable_items:
                return
            self._remove_selected(list(removable_items))
            refresh()

        refresh()
        btn_remove.clicked.connect(on_remove_clicked)
        btn_close.clicked.connect(dialog.close)
        dialog.exec()

    # Build and handle the right-click context menu for the URL/folder tree
    def _on_url_list_context_menu(self, pos):
        item_at_pos = self.url_list.itemAt(pos)
        # Empty space (no link/folder under the cursor): a background-only menu,
        # not the full per-item one.
        if item_at_pos is None:
            self._show_url_list_background_menu(pos)
            return
        if item_at_pos.data(0, IS_LOAD_MORE_ROLE):
            self._show_load_more_context_menu(item_at_pos, pos)
            return
        if item_at_pos not in self.url_list.selectedItems():
            self.url_list.setCurrentItem(item_at_pos)
        selected = self.url_list.selectedItems()
        if not selected:
            self._show_url_list_background_menu(pos)
            return

        has_links = bool(self._expand_links(selected))
        has_disabled = any(it.data(0, LINK_DISABLED_ROLE) for it in selected)
        has_enabled = any(
            not it.data(0, LINK_DISABLED_ROLE)
            and (it.data(0, IS_FOLDER_ROLE) or it.data(0, DOWNLOAD_PROGRESS_ROLE) != 100)
            for it in selected
        )
        has_skipped = any(it.data(0, LINK_SKIPPED_ROLE) for it in selected)
        has_unskipped = any(
            not it.data(0, LINK_SKIPPED_ROLE)
            and (it.data(0, IS_FOLDER_ROLE) or it.data(0, DOWNLOAD_PROGRESS_ROLE) != 100)
            for it in selected
        )
        has_folder_selected = any(it.data(0, IS_FOLDER_ROLE) for it in selected)
        is_single_folder = len(selected) == 1 and selected[0].data(0, IS_FOLDER_ROLE)
        is_subgroup_channel_folder = False
        if is_single_folder:
            profile = self._current_profile_dict()
            if profile and profile.get("type") == "Sub Group":
                folder_name = selected[0].data(0, RAW_TEXT_ROLE)
                is_subgroup_channel_folder = any(
                    c.get("name") == folder_name for c in (profile.get("channels") or [])
                )
        can_move_up = any(
            self._sibling_index(it.parent(), it) > 0 for it in selected
        )
        can_move_down = any(
            self._sibling_index(it.parent(), it) < self._sibling_count(it.parent()) - 1
            for it in selected
        )

        menu = QMenu(self)
        menu.setStyleSheet(menu_style())

        act_search = menu.addAction("Search")
        menu.addSeparator()

        act_up = menu.addAction("Move up")
        act_up.setEnabled(can_move_up)
        act_down = menu.addAction("Move down")
        act_down.setEnabled(can_move_down)
        act_top = menu.addAction("Move to top")
        act_top.setEnabled(can_move_up)
        # Folders can't be nested inside another folder, so "Move to folder" only makes
        # sense for a link-only selection; a lone folder gets "Rename folder" instead.
        act_move_folder = menu.addAction("Move to folder") if not has_folder_selected else None
        act_rename_folder = menu.addAction("Rename folder") if is_single_folder else None
        act_set_folder_quality = (
            menu.addAction("Set quality...") if is_subgroup_channel_folder else None
        )

        act_expand_all = None
        act_collapse_all = None
        if has_folder_selected and self._has_any_folder():
            menu.addSeparator()
            act_expand_all = menu.addAction("Expand all folders")
            act_collapse_all = menu.addAction("Collapse all folders")

        menu.addSeparator()
        act_enable = menu.addAction("Enable") if has_disabled else None
        act_disable = menu.addAction("Disable") if has_enabled else None
        act_skip = menu.addAction("Skip") if has_unskipped else None
        act_unskip = menu.addAction("Unskip") if has_skipped else None

        menu.addSeparator()
        act_retry = menu.addAction("Retry probe")
        act_retry.setEnabled(has_links)
        act_reset = menu.addAction("Reset")
        act_reset.setEnabled(has_links)
        act_force_quality = menu.addAction("Force quality...")
        act_force_quality.setEnabled(has_links)
        act_get_link = menu.addAction("Get link")
        act_get_link.setEnabled(has_links)
        act_open_folder = menu.addAction("Open in folder")
        act_open_folder.setEnabled(len(selected) == 1)

        menu.addSeparator()
        act_remove = menu.addAction("Remove")

        action = menu.exec(self.url_list.viewport().mapToGlobal(pos))
        if action == act_search:
            self._show_search_dialog()
        elif action == act_up:
            self._move_selected_up(selected)
        elif action == act_down:
            self._move_selected_down(selected)
        elif action == act_top:
            self._move_selected_to_top(selected)
        elif act_move_folder is not None and action == act_move_folder:
            self._move_selected_to_folder(selected)
        elif act_rename_folder is not None and action == act_rename_folder:
            self._rename_folder(selected[0])
        elif act_set_folder_quality is not None and action == act_set_folder_quality:
            self._set_folder_quality(selected[0])
        elif act_expand_all is not None and action == act_expand_all:
            self._expand_all_folders()
        elif act_collapse_all is not None and action == act_collapse_all:
            self._collapse_all_folders()
        elif act_enable is not None and action == act_enable:
            self._set_selected_enabled(selected, True)
        elif act_disable is not None and action == act_disable:
            self._set_selected_enabled(selected, False)
        elif act_skip is not None and action == act_skip:
            self._set_selected_skipped(selected, True)
        elif act_unskip is not None and action == act_unskip:
            self._set_selected_skipped(selected, False)
        elif action == act_retry:
            self._retry_selected(selected)
        elif action == act_reset:
            self._reset_selected(selected)
        elif action == act_force_quality:
            self._force_quality_selected(selected)
        elif action == act_get_link:
            self._get_link_selected(selected)
        elif action == act_open_folder:
            self._open_in_folder_selected(selected)
        elif action == act_remove:
            self._remove_selected(selected)

    # Number of children under a tree parent, or top-level item count if parent is None
    def _sibling_count(self, parent):
        if parent is None:
            return self.url_list.topLevelItemCount()
        return parent.childCount()

    # Build (or, if already open, just refocus) the non-modal "Search links" dialog:
    # paste a URL or a name and jump straight to it, even if it's still paginated
    # out of the tree behind a "Load more" sentinel.
    def _show_search_dialog(self):
        if getattr(self, "_search_dialog", None) is not None:
            self._search_dialog.show()
            self._search_dialog.raise_()
            self._search_dialog.activateWindow()
            self._search_edit.setFocus()
            self._search_edit.selectAll()
            return

        dialog = QDialog(self)
        dialog.setWindowTitle("Search links")
        dialog.setMinimumWidth(420)
        layout = QVBoxLayout(dialog)

        mode_row = QHBoxLayout()
        mode_label = QLabel("Search by:")
        mode_label.setStyleSheet(sidebar_label_muted_style())
        mode_row.addWidget(mode_label)
        self._search_mode_name_radio = QRadioButton("Name")
        self._search_mode_name_radio.setStyleSheet(radio_button_style())
        self._search_mode_url_radio = QRadioButton("URL")
        self._search_mode_url_radio.setStyleSheet(radio_button_style())
        self._search_mode_name_radio.setChecked(True)
        self._search_mode_group = QButtonGroup(dialog)
        self._search_mode_group.addButton(self._search_mode_name_radio)
        self._search_mode_group.addButton(self._search_mode_url_radio)
        mode_row.addWidget(self._search_mode_name_radio)
        mode_row.addWidget(self._search_mode_url_radio)
        mode_row.addStretch()
        layout.addLayout(mode_row)

        self._search_edit = QLineEdit()
        self._search_edit.setStyleSheet(line_edit_style())
        layout.addWidget(self._search_edit)

        self._search_status_label = QLabel("")
        self._search_status_label.setStyleSheet(sidebar_label_muted_style())
        layout.addWidget(self._search_status_label)

        row = QHBoxLayout()
        btn_find = QPushButton("Find")
        btn_find.setStyleSheet(button_style())
        self._search_find_btn = btn_find
        self._search_next_btn = QPushButton("Next")
        self._search_next_btn.setStyleSheet(button_style())
        self._search_next_btn.setEnabled(False)
        btn_close = QPushButton("Close")
        btn_close.setStyleSheet(button_style())
        row.addWidget(btn_find)
        row.addWidget(self._search_next_btn)
        row.addStretch()
        row.addWidget(btn_close)
        layout.addLayout(row)

        self._search_matches = []
        self._search_match_index = -1
        self._search_is_link_mode = False

        self._search_mode_name_radio.toggled.connect(self._update_search_placeholder)
        self._update_search_placeholder()
        self._search_edit.returnPressed.connect(self._on_search_triggered)
        btn_find.clicked.connect(self._on_search_triggered)
        self._search_next_btn.clicked.connect(self._on_search_next)
        btn_close.clicked.connect(dialog.close)
        dialog.finished.connect(self._on_search_dialog_closed)

        self._search_dialog = dialog
        dialog.show()
        self._search_edit.setFocus()

    # Swap the search box's placeholder to match whichever mode (Name/URL) is
    # currently selected, so it's clear what kind of text to paste
    def _update_search_placeholder(self):
        if self._search_mode_name_radio.isChecked():
            self._search_edit.setPlaceholderText("Type or paste a name to search for")
        else:
            self._search_edit.setPlaceholderText("Paste a URL to search for")

    # Drop the reference to the search dialog once it's closed, so the next
    # "Search" click builds a fresh one instead of reusing stale widgets
    def _on_search_dialog_closed(self, result=None):
        self._search_dialog = None

    # Run (or re-run) a search for whatever's currently in the search box, restricted
    # to whichever mode (Name/URL) is selected in the dialog. In URL mode "Next" is
    # enabled (the point of that mode is cycling through duplicate/similar URLs); a
    # name search just jumps to the first hit and "Next" stays off unless there's more
    # than one match. Materializing the whole tree first (so paginated-out links are
    # included) can take a moment on a large list, so the box shows "Searching..." and
    # a busy cursor while it works.
    def _on_search_triggered(self):
        query = self._search_edit.text().strip()
        if not query:
            self._search_status_label.setText("")
            self._search_matches = []
            self._search_match_index = -1
            self._search_next_btn.setEnabled(False)
            return

        is_link_mode = self._search_mode_url_radio.isChecked()

        self._search_status_label.setText("Searching…")
        self._search_find_btn.setEnabled(False)
        self._search_next_btn.setEnabled(False)
        QApplication.processEvents()
        QApplication.setOverrideCursor(Qt.WaitCursor)
        try:
            self._materialize_entire_tree()

            query_lower = query.lower()
            matches = []
            for item in self._iter_all_link_items():
                if is_link_mode:
                    url = item.data(0, URL_ROLE) or ""
                    if self._search_urls_match(url, query):
                        matches.append(item)
                else:
                    candidates = (item.data(0, TITLE_ROLE), item.data(0, RAW_TEXT_ROLE), item.text(0))
                    if any(c and query_lower in c.lower() for c in candidates):
                        matches.append(item)
        finally:
            QApplication.restoreOverrideCursor()
            self._search_find_btn.setEnabled(True)

        self._search_matches = matches
        self._search_match_index = 0 if matches else -1
        self._search_is_link_mode = is_link_mode
        self._search_next_btn.setEnabled(len(matches) > 1)

        if not matches:
            self._search_status_label.setText("No matches found")
            return

        self._search_status_label.setText(f"Match 1 of {len(matches)}")
        self._highlight_search_match(matches[0])

    # Whether a link's stored URL matches a pasted/typed query, for URL-mode search.
    # Tries a plain substring match first (either direction, so a query with extra
    # tracking params, or a stored URL that's a prefix of a longer pasted one, still
    # hits), then falls back to comparing YouTube video IDs - the same trick used
    # elsewhere (see _youtube_video_id) to treat differently-formatted URLs for the
    # same video (youtu.be vs youtube.com/watch, webpage_url vs a bare ID, etc.) as
    # equivalent, so a link that was probed and renamed to its title can still be
    # found by pasting its URL back in.
    def _search_urls_match(self, stored_url, query):
        if not stored_url:
            return False
        stored_lower = stored_url.lower()
        query_lower = query.lower()
        if query_lower in stored_lower or stored_lower in query_lower:
            return True
        stored_id = _youtube_video_id(stored_url)
        query_id = _youtube_video_id(query)
        return bool(stored_id) and stored_id == query_id

    # Jump to the next result, wrapping back to the first after the last
    def _on_search_next(self):
        if not self._search_matches:
            return
        self._search_match_index = (self._search_match_index + 1) % len(self._search_matches)
        self._search_status_label.setText(
            f"Match {self._search_match_index + 1} of {len(self._search_matches)}"
        )
        self._highlight_search_match(self._search_matches[self._search_match_index])

    # Expand every ancestor folder so the match is actually visible, then select
    # and scroll to it
    def _highlight_search_match(self, item):
        ancestor = item.parent()
        while ancestor is not None:
            ancestor.setExpanded(True)
            ancestor = ancestor.parent()
        self.url_list.setCurrentItem(item)
        self.url_list.scrollToItem(item, QAbstractItemView.PositionAtCenter)

    # Index of an item among its siblings under the given parent
    def _sibling_index(self, parent, item):
        if parent is None:
            return self.url_list.indexOfTopLevelItem(item)
        return parent.indexOfChild(item)

    # Remove and return the sibling at index under the given parent
    def _take_sibling(self, parent, index):
        if parent is None:
            return self.url_list.takeTopLevelItem(index)
        return parent.takeChild(index)

    # Insert an item at index under the given parent
    def _insert_sibling(self, parent, index, item):
        if parent is None:
            self.url_list.insertTopLevelItem(index, item)
        else:
            parent.insertChild(index, item)

    # Group tree items by parent and sort each group by sibling order
    def _group_by_parent(self, items):
        groups = {}
        for item in items:
            groups.setdefault(item.parent(), []).append(item)
        for parent, group in groups.items():
            group.sort(key=lambda it: self._sibling_index(parent, it))
        return groups

    # Handles "+"/"-" pressed in the tree (see DraggableTreeWidget.keyPressEvent) -
    # moves the current selection up/down, same as the right-click Move up/down actions
    def _on_url_list_move_key(self, direction):
        selected = self.url_list.selectedItems()
        if not selected:
            return
        if direction == "up":
            self._move_selected_up(selected)
        else:
            self._move_selected_down(selected)

    # Move each selected item one position up among its siblings
    def _move_selected_up(self, items):
        for parent, group in self._group_by_parent(items).items():
            for item in group:
                index = self._sibling_index(parent, item)
                if index <= 0:
                    continue
                expanded = item.isExpanded()
                moved = self._take_sibling(parent, index)
                self._insert_sibling(parent, index - 1, moved)
                moved.setExpanded(expanded)
                moved.setSelected(True)
        self._renumber_url_list()

    # Move each selected item one position down among its siblings
    def _move_selected_down(self, items):
        for parent, group in self._group_by_parent(items).items():
            for item in reversed(group):
                index = self._sibling_index(parent, item)
                if index == -1 or index >= self._sibling_count(parent) - 1:
                    continue
                expanded = item.isExpanded()
                moved = self._take_sibling(parent, index)
                self._insert_sibling(parent, index + 1, moved)
                moved.setExpanded(expanded)
                moved.setSelected(True)
        self._renumber_url_list()

    # Move each selected item to the top of its sibling group
    def _move_selected_to_top(self, items):
        for parent, group in self._group_by_parent(items).items():
            for offset, item in enumerate(group):
                index = self._sibling_index(parent, item)
                if index == offset:
                    continue
                expanded = item.isExpanded()
                moved = self._take_sibling(parent, index)
                self._insert_sibling(parent, offset, moved)
                moved.setExpanded(expanded)
                moved.setSelected(True)
        self._renumber_url_list()

    # Enable or disable selected items and all of their descendants
    def _set_selected_enabled(self, items, enabled):
        # Recursively enable/disable this item and all its children, except a link
        # that's already fully downloaded - nothing left for disabling it to prevent
        def apply(item):
            if not item.data(0, IS_FOLDER_ROLE) and item.data(0, DOWNLOAD_PROGRESS_ROLE) == 100:
                return
            item.setData(0, LINK_DISABLED_ROLE, not enabled)
            for i in range(item.childCount()):
                apply(item.child(i))

        was_downloading = bool(self._download_tasks)
        for item in items:
            apply(item)
            if not enabled:
                self._cancel_probes_for_item(item)
                self._cancel_download_for_item(item)
        state = "Enabled" if enabled else "Disabled"
        self._save_links_to_disk()
        self._log(f"{state} {len(items)} item(s)")
        self._update_download_button()
        if not enabled and was_downloading:
            self._start_downloads(quiet=True)

    # Mark selected items (and descendants) as "Skip" placeholders, or clear that
    # flag. A skipped link stays in the tree - so it still counts toward a
    # Refresh's "already known" video-ID set (see
    # _existing_channel_video_ids/_existing_channel_video_ids_in_folder) and keeps
    # its place for upload-order purposes - but it's excluded from downloading and
    # from numbering (see _start_downloads/_update_download_button and
    # _renumber_siblings/_subgroup_upload_order_map).
    def _set_selected_skipped(self, items, skipped):
        # Recursively mark this item and all its children as skipped/not skipped,
        # except a link that's already fully downloaded - nothing left for
        # skipping it to prevent
        def apply(item):
            if not item.data(0, IS_FOLDER_ROLE) and item.data(0, DOWNLOAD_PROGRESS_ROLE) == 100:
                return
            item.setData(0, LINK_SKIPPED_ROLE, skipped)
            for i in range(item.childCount()):
                apply(item.child(i))

        was_downloading = bool(self._download_tasks)
        for item in items:
            apply(item)
            if skipped:
                self._cancel_download_for_item(item)
        state = "Marked as skip" if skipped else "Unskipped"
        self._renumber_url_list()
        self._refresh_skip_visibility()
        self._log(f"{state} {len(items)} item(s)")
        if skipped and was_downloading:
            self._start_downloads(quiet=True)

    # Expand a selection into the actual link items it refers to: a link stands for
    # itself, a folder stands for every link nested inside it (recursively). Used so
    # actions like retry/force-quality apply to a whole folder's contents, not just
    # to links that happen to be individually selected.
    def _expand_links(self, items):
        seen = set()
        links = []

        # Recursively gather every non-folder link item under this item, without duplicates
        def collect(item):
            if item.data(0, IS_FOLDER_ROLE):
                for i in range(item.childCount()):
                    collect(item.child(i))
            elif id(item) not in seen:
                seen.add(id(item))
                links.append(item)

        for item in items:
            collect(item)
        return links

    # Collect the LINK_UUID_ROLE of item itself (if a link) or every link nested inside
    # it (if a folder), used to clean up cached thumbnails when items are deleted
    def _collect_link_uuids(self, item):
        if item.data(0, IS_FOLDER_ROLE):
            uuids = []
            for i in range(item.childCount()):
                uuids += self._collect_link_uuids(item.child(i))
            return uuids
        link_uuid = item.data(0, LINK_UUID_ROLE)
        return [link_uuid] if link_uuid else []

    # Stop any in-flight probe or playlist listing running for this item or any of its
    # descendants (e.g. a folder whose children are still being probed), killing the
    # underlying yt-dlp process rather than letting it run to completion for nothing.
    def _cancel_probes_for_item(self, item):
        task = self._tasks_by_item.pop(id(item), None)
        if task is not None:
            task.cancel()
            if task is self._channel_refresh_task:
                self._channel_refresh_task = None
                self._refresh_task_finished()
                self._update_refresh_button()
            else:
                self._probe_finished()
        for i in range(item.childCount()):
            self._cancel_probes_for_item(item.child(i))

    # Cancel any in-flight download task for this item (and its descendants, if a
    # folder), killing the underlying yt-dlp process rather than letting it finish
    def _cancel_download_for_item(self, item):
        task = self._download_tasks.pop(id(item), None)
        if task is not None:
            task.cancel()
        self._download_retry_counts.pop(id(item), None)
        if self._download_timeouts.pop(id(item), None) is not None:
            item.setData(0, DOWNLOAD_TIMEOUT_ROLE, None)
        for i in range(item.childCount()):
            self._cancel_download_for_item(item.child(i))

    # Find the active Channel profile's tracking folder in the tree without creating
    # it (unlike _get_or_create_channel_folder). Returns None if there isn't one.
    def _find_channel_folder(self, profile):
        return self._find_folder_by_name(profile.get("name"))

    # Return the id()s of the link(s) that are the most recent tracking anchor within
    # a single folder - i.e. what a future "Refresh" treats as the newest video
    # appended so far for whatever that folder tracks. Determined by comparing each
    # child's probed UPLOAD_DATE_ROLE ("YYYY.MM.DD", lexicographically sortable)
    # rather than tree position, since links can be manually reordered (Move
    # Up/Down/Top) away from the order they were actually appended in. Falls back to
    # position (index 0) only when no child has a probed date yet - new links are
    # always inserted at the top of the folder (see _on_channel_refresh_finished).
    def _most_recent_link_ids_in_folder(self, folder):
        dated_children = []
        for i in range(folder.childCount()):
            child = folder.child(i)
            date = child.data(0, UPLOAD_DATE_ROLE)
            if date:
                dated_children.append((child, date))

        if dated_children:
            newest_date = max(date for _child, date in dated_children)
            return {id(child) for child, date in dated_children if date == newest_date}

        if folder.childCount() > 0:
            return {id(folder.child(0))}
        return set()

    # Return the id()s of the link(s) that are the most recent tracking anchor(s) for
    # the active profile - i.e. what a future "Refresh" treats as the newest video(s)
    # already appended. For a Channel profile that's just the one tracking folder;
    # for a Sub Group it's every one of its channels' own folders, each checked
    # independently, since each channel is refreshed (and tracked) separately. The
    # relevant folder(s) are scanned exactly once here, regardless of how many items
    # are being deleted - so a bulk delete costs the same single pass as a
    # single-item delete.
    def _most_recent_channel_link_ids(self):
        profile = self._current_profile_dict()
        if not profile:
            return set()
        ptype = profile.get("type")
        if ptype == "Channel":
            folder = self._find_channel_folder(profile)
            if folder is None:
                return set()
            return self._most_recent_link_ids_in_folder(folder)
        if ptype == "Sub Group":
            ids = set()
            for channel in profile.get("channels") or []:
                folder = self._find_folder_by_name(channel.get("name"))
                if folder is not None:
                    ids |= self._most_recent_link_ids_in_folder(folder)
            return ids
        return set()

    # Remove selected items from the tree, skipping items whose ancestor is also selected
    def _remove_selected(self, items):
        selected_ids = {id(it) for it in items}

        # True if any ancestor of item is also selected, meaning it'll be moved/removed
        # along with that ancestor already
        def has_selected_ancestor(item):
            parent = item.parent()
            while parent is not None:
                if id(parent) in selected_ids:
                    return True
                parent = parent.parent()
            return False

        to_remove = [it for it in items if not has_selected_ancestor(it)]
        if not to_remove:
            return

        most_recent_ids = self._most_recent_channel_link_ids()
        caught = [it for it in to_remove if id(it) in most_recent_ids]
        if caught:
            if not self._confirm_most_recent_channel_link_removal(bulk=len(to_remove) > 1):
                return

        has_folder = any(it.data(0, IS_FOLDER_ROLE) for it in to_remove)
        if len(to_remove) == 1:
            kind = "folder" if to_remove[0].data(0, IS_FOLDER_ROLE) else "link"
            name = to_remove[0].text(0)
            message = f"Remove {kind} '{name}'?"
            if kind == "folder":
                message += " This will also remove everything inside it."
        else:
            message = f"Remove {len(to_remove)} selected item(s)?"
            if has_folder:
                message += " Any selected folders will also remove everything inside them."
        delete_from_disk = self._confirm_removal(message)
        if delete_from_disk is None:
            return

        for item in to_remove:
            self._cancel_probes_for_item(item)
            self._cancel_download_for_item(item)
            for link_uuid in self._collect_link_uuids(item):
                remove_thumbnail(link_uuid)
            if delete_from_disk:
                self._delete_files_from_disk(item)
            parent = item.parent()
            index = self._sibling_index(parent, item)
            if index != -1:
                self._take_sibling(parent, index)
        self._renumber_url_list()
        suffix = " and deleted from disk" if delete_from_disk else ""
        self._log(f"Removed {len(to_remove)} item(s){suffix}")
        self._on_url_list_selection_changed()

    # Show a blocking "ATTENTION" warning before deleting the most recent link in a
    # Channel profile, since that link is what a future Refresh uses to know which
    # videos have already been appended. Returns True if the user confirms.
    def _confirm_most_recent_channel_link_removal(self, bulk=False):
        box = QMessageBox(self)
        box.setIcon(QMessageBox.Warning)
        box.setWindowTitle("Attention")
        if bulk:
            text = (
                "ATTENTION! Your selection includes the most recent dates, which is "
                "used to track the videos to append, are you sure you want to delete it?"
            )
        else:
            text = (
                "ATTENTION! This is the most recent date, which is used to track "
                "the videos to append, are you sure you want to delete it?"
            )
        box.setText(text)
        box.setStandardButtons(QMessageBox.Yes | QMessageBox.No)
        box.setDefaultButton(QMessageBox.No)
        return box.exec() == QMessageBox.Yes

    # Show a removal confirmation dialog with a "delete from disk" checkbox (off by
    # default) to the left of the OK/Cancel buttons. Returns None if the user
    # cancels, otherwise a bool for whether the checkbox was checked.
    def _confirm_removal(self, message, title="Remove", checkbox_label="Also delete from disk"):
        dialog = QDialog(self)
        dialog.setWindowTitle(title)
        dialog.setMinimumSize(500, 75)
        layout = QVBoxLayout(dialog)
        label = QLabel(message)
        label.setWordWrap(True)
        layout.addWidget(label)

        row = QHBoxLayout()
        delete_checkbox = QCheckBox(checkbox_label)
        delete_checkbox.setChecked(False)
        delete_checkbox.setStyleSheet(checkbox_style())
        row.addWidget(delete_checkbox)
        row.addStretch()
        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(dialog.accept)
        buttons.rejected.connect(dialog.reject)
        row.addWidget(buttons)
        layout.addLayout(row)

        if dialog.exec() != QDialog.Accepted:
            return None
        return delete_checkbox.isChecked()

    # Delete the downloaded video file for this item from disk, recursing into
    # children if it's a folder. Missing files/paths are silently skipped. For a
    # folder, once every child's file is gone we try to remove the folder's own
    # on-disk directory too, but only if that leaves it empty - see
    # _delete_folder_dir_from_disk. This way any user-added or renamed files/folders
    # left inside are preserved instead of being swept away.
    def _delete_files_from_disk(self, item):
        if item.data(0, IS_FOLDER_ROLE):
            for i in range(item.childCount()):
                self._delete_files_from_disk(item.child(i))
            self._delete_folder_dir_from_disk(item)
            return
        path_str = item.data(0, DOWNLOAD_PATH_ROLE)
        if not path_str:
            return
        path = Path(path_str)
        try:
            if path.exists():
                path.unlink()
        except OSError as e:
            self._log(f"Failed to delete file from disk: {path} ({e})")

    # Remove the on-disk directory that backs a folder tree item (location/<folder name>),
    # if it exists. Called after every child link's file has already been deleted.
    # Only removes the directory itself if that deletion left it empty - if the user
    # had added or renamed files/folders inside it, those are left untouched and the
    # directory is left behind with an error logged instead of being wiped via rmtree.
    def _delete_folder_dir_from_disk(self, folder_item):
        location = self.location_edit.text().strip()
        name = folder_item.data(0, RAW_TEXT_ROLE) or folder_item.text(0)
        if not location or not name:
            return
        folder_dir = Path(location) / _sanitize_profile_name(name)
        if not folder_dir.is_dir():
            return
        try:
            folder_dir.rmdir()
        except OSError:
            if any(folder_dir.iterdir()):
                self._log(
                    f"Folder not empty, left on disk: {folder_dir} "
                    "(contains user-added or renamed files/folders)"
                )
            else:
                self._log(f"Failed to remove folder from disk: {folder_dir}")

    # Re-queue a probe for the selected links (their URL is unaffected by any renaming)
    def _retry_selected(self, items):
        links = self._expand_links(items)
        if not links:
            return
        for item in links:
            self._start_probe(item)
        self._log(f"Retry requested for {len(links)} link(s)")

    # Stop any in-flight download and clear a link's download-progress state (hiding
    # the "N% - " it adds to the row), then re-run its probe from scratch
    def _reset_selected(self, items):
        links = [it for it in items if not it.data(0, IS_FOLDER_ROLE)]
        if not links:
            return
        for item in links:
            self._cancel_download_for_item(item)
            item.setData(0, DOWNLOAD_PROGRESS_ROLE, None)
            item.setData(0, LINK_NUMBERING_RESET_ROLE, False)
            item.setData(0, TITLE_ROLE, None)
            link_uuid = item.data(0, LINK_UUID_ROLE)
            if link_uuid:
                self.set_download_speed(link_uuid, 0)
        self._update_sidebar_info()
        self._update_download_button()
        self._renumber_url_list()
        for item in links:
            self._start_probe(item)
        self._log(f"Reset {len(links)} link(s) and retried probe")

    # Prompt for a quality override and apply it to the selected links
    def _force_quality_selected(self, items):
        links = self._expand_links(items)
        if not links:
            return
        qualities = [
            "Audio only", "144p", "240p", "360p", "480p", "720p",
            "1080p", "1440p (2K)", "2160p (4K)", "Best available",
        ]
        quality, ok = QInputDialog.getItem(
            self, "Force quality", "Quality:", qualities, editable=False
        )
        if not ok:
            return
        for item in links:
            item.setData(0, FORCED_QUALITY_ROLE, quality)
            item.setData(0, FORCE_QUALITY_PENDING_ROLE, True)
        self._renumber_url_list()
        for item in links:
            self._start_probe(item)
        self._log(f"Forced quality '{quality}' for {len(links)} link(s), re-probing")

    # Prompt for a quality override for one Sub Group channel folder and persist it
    # onto that channel's own "quality" entry in the profile's "channels" metadata -
    # so from now on, new videos discovered for just this channel probe at that
    # quality, while every other channel in the same sub group is unaffected. Unlike
    # "Force quality...", this doesn't touch (or re-probe) any video already sitting
    # in the folder - it only changes what NEW ones default to; use "Force
    # quality..." on the folder as well if the already-probed videos should also
    # switch over.
    def _set_folder_quality(self, folder_item):
        profile = self._current_profile_dict()
        if not profile or profile.get("type") != "Sub Group":
            return
        name = folder_item.data(0, RAW_TEXT_ROLE)
        channels = profile.get("channels") or []
        channel = next((c for c in channels if c.get("name") == name), None)
        if channel is None:
            return
        qualities = [
            "Audio only", "144p", "240p", "360p", "480p", "720p",
            "1080p", "1440p (2K)", "2160p (4K)", "Best available",
        ]
        current = channel.get("quality") or self.quality_combo.currentText()
        current_index = qualities.index(current) if current in qualities else 0
        quality, ok = QInputDialog.getItem(
            self, "Set channel quality", f"Quality for '{name}':", qualities,
            current_index, editable=False,
        )
        if not ok:
            return
        channel["quality"] = quality
        folder_item.setData(0, FOLDER_QUALITY_ROLE, quality)
        save_profile_metadata(
            profile["name"], profile.get("type"), profile.get("channel_url"),
            channels, profile.get("number_by_upload_order"),
        )
        self._on_url_list_selection_changed()
        self._log(f"Set quality for channel '{name}' to '{quality}'")

    # Copy the selected links' URLs to the clipboard
    def _get_link_selected(self, items):
        urls = [it.data(0, URL_ROLE) for it in items if not it.data(0, IS_FOLDER_ROLE)]
        if not urls:
            return
        QGuiApplication.clipboard().setText("\n".join(urls))
        self._log(f"Copied {len(urls)} link(s) to clipboard")

    # Open each selected item's own folder in the OS file browser, highlighting the
    # downloaded file itself where one exists - rather than always opening the root
    # download location, which left the user to go hunt for the file by hand any
    # time it lived in a subfolder (or just to see which of several same-named-ish
    # links a row actually corresponds to).
    def _open_in_folder_selected(self, items):
        location = self.location_edit.text().strip()
        if not location:
            self._log("Open in folder: no download location is set")
            return
        opened = 0
        for item in items:
            if item.data(0, IS_FOLDER_ROLE):
                folder_name = self._effective_download_folder_name(item.data(0, RAW_TEXT_ROLE))
                target_dir = self._download_dest_dir_for_folder(folder_name, location)
                if not _reveal_path(target_dir):
                    self._log(f"Open in folder: couldn't open {target_dir}")
                    continue
                opened += 1
                continue
            download_path = item.data(0, DOWNLOAD_PATH_ROLE)
            if download_path and Path(download_path).exists():
                target = download_path
            else:
                # Not downloaded yet (or the file's gone missing) - fall back to
                # just opening the folder it's slated to land in / was downloaded into.
                target = self._download_dest_dir_for_item(item, location)
            if not _reveal_path(target):
                self._log(f"Open in folder: couldn't open {target}")
                continue
            opened += 1
        if opened:
            self._log_detailed(f"Opened folder for {opened} item(s)")

    # Open a native "choose folder" dialog for the download location setting,
    # starting from the currently configured location (if any)
    def _on_browse_location(self):
        start_dir = self.location_edit.text().strip() or str(Path.home())
        chosen = QFileDialog.getExistingDirectory(self, "Choose download location", start_dir)
        if not chosen:
            return
        self.location_edit.setText(chosen)
        self._log(f"Download location set to: {chosen}")

    # Prompt for a folder name and move the selected items into a new folder item
    # Rename a folder in the tree, and if a matching folder already exists in the
    # download location, rename that too and update every child link's tracked
    # download path so it still points at the right (moved) file.
    def _rename_folder(self, folder):
        old_name = folder.data(0, RAW_TEXT_ROLE) or ""
        new_name, ok = QInputDialog.getText(self, "Rename folder", "Folder name:", text=old_name)
        new_name = new_name.strip()
        if not ok or not new_name or new_name == old_name:
            return

        profile = self._current_profile_dict()
        channels = (profile.get("channels") or []) if profile else []
        is_subgroup_channel = bool(
            profile and profile.get("type") == "Sub Group"
            and any(c.get("name") == old_name for c in channels)
        )
        if is_subgroup_channel and any(c.get("name") == new_name for c in channels):
            self._log(f"Rename folder: '{new_name}' is already a channel in this sub group")
            return

        # A Sub Group channel folder's files all live in the shared group folder (see
        # _effective_download_folder_name), not in a folder of their own on disk, so
        # there's no per-channel directory to rename - only every other folder kind
        # (Channel/Playlist folders, or one made by hand) gets that disk-rename step.
        if not is_subgroup_channel:
            location = self.location_edit.text().strip()
            if location:
                old_dir = Path(location) / _sanitize_profile_name(old_name)
                new_dir = Path(location) / _sanitize_profile_name(new_name)
                if old_dir.is_dir() and old_dir != new_dir:
                    if new_dir.exists():
                        self._log(
                            f"Rename folder: '{new_dir.name}' already exists in the download "
                            "location, so downloaded files were left where they were"
                        )
                    else:
                        try:
                            old_dir.rename(new_dir)
                            self._update_download_paths_for_renamed_folder(folder, old_dir, new_dir)
                        except OSError as exc:
                            self._log(f"Rename folder: couldn't rename download folder: {exc}")

        folder.setData(0, RAW_TEXT_ROLE, new_name)
        if is_subgroup_channel:
            for c in channels:
                if c.get("name") == old_name:
                    c["name"] = new_name
                    break
            save_profile_metadata(
                profile["name"], profile.get("type"), profile.get("channel_url"), channels,
                profile.get("number_by_upload_order"),
            )
            self._reload_subgroup_channel_list()
        self._renumber_url_list()
        self._log(f"Renamed folder to '{new_name}'")

    # After a folder's on-disk directory is renamed, point every child link's tracked
    # download path at the same file under the new directory instead of the old one
    def _update_download_paths_for_renamed_folder(self, folder, old_dir, new_dir):
        for i in range(folder.childCount()):
            child = folder.child(i)
            if child.data(0, IS_FOLDER_ROLE):
                continue
            path_str = child.data(0, DOWNLOAD_PATH_ROLE)
            if not path_str:
                continue
            try:
                rel = Path(path_str).relative_to(old_dir)
            except ValueError:
                continue
            child.setData(0, DOWNLOAD_PATH_ROLE, str(new_dir / rel))

    # Create a new folder and move the selected items into it
    def _move_selected_to_folder(self, items):
        name, ok = QInputDialog.getText(
            self, "Move to folder", "Folder name:", text="New Folder"
        )
        name = name.strip()
        if not ok or not name:
            return

        folder_item = QTreeWidgetItem()
        folder_item.setData(0, RAW_TEXT_ROLE, name)
        folder_item.setData(0, IS_FOLDER_ROLE, True)
        self._apply_item_flags(folder_item)
        self.url_list.addTopLevelItem(folder_item)

        before_parents = []
        for item in items:
            if item is folder_item:
                continue
            parent = item.parent()
            before_parents.append((item, parent))
            if parent is not None:
                parent.removeChild(item)
            else:
                index = self.url_list.indexOfTopLevelItem(item)
                if index != -1:
                    self.url_list.takeTopLevelItem(index)
            folder_item.addChild(item)

        folder_item.setExpanded(True)
        self._relocate_dropped_files(before_parents)
        self._renumber_url_list()
        self._log_detailed(f"Moved {len(items)} item(s) into folder '{name}'")

    # Set the flags that control this item's drag-and-drop behavior: every row can be
    # selected and dragged, but only folders can have something dropped "on" them (i.e.
    # nested inside as a new child) - a link row lacks Qt.ItemIsDropEnabled, so Qt
    # resolves a drop hovering over it into an above/below reorder instead of nesting.
    def _apply_item_flags(self, item):
        flags = Qt.ItemIsSelectable | Qt.ItemIsEnabled | Qt.ItemIsDragEnabled
        if item.data(0, IS_FOLDER_ROLE):
            flags |= Qt.ItemIsDropEnabled
        item.setFlags(flags)

    # Called after the user drags-and-drops rows in the URL tree to reorder/move them;
    # Qt has already performed the actual move by this point. before_parents is the
    # list of (item, old_parent) pairs captured just before the move.
    def _on_url_list_dropped(self, before_parents=None):
        if before_parents:
            self._relocate_dropped_files(before_parents)
        self._renumber_url_list()
        self._on_url_list_selection_changed()
        self._log("Reordered link(s)/folder(s)")

    # For every dragged item whose containing folder actually changed, move its
    # already-downloaded file (if any) from the old destination folder to the new
    # one on disk, in real time - a folder move is a plain filesystem move, no
    # re-download needed. Dragging a folder itself relocates every link inside it.
    def _relocate_dropped_files(self, before_parents):
        location = self.location_edit.text().strip()
        if not location:
            return
        for item, old_parent in before_parents:
            self._relocate_item_file(item, old_parent, location)

    # Move a link's already-downloaded file on disk to match its new folder after
    # a drag-and-drop move
    def _relocate_item_file(self, item, old_parent, location):
        if item.data(0, IS_FOLDER_ROLE):
            for i in range(item.childCount()):
                self._relocate_item_file(item.child(i), old_parent, location)
            return
        old_folder = old_parent.data(0, RAW_TEXT_ROLE) if (old_parent and old_parent.data(0, IS_FOLDER_ROLE)) else None
        new_parent = item.parent()
        new_folder = new_parent.data(0, RAW_TEXT_ROLE) if (new_parent and new_parent.data(0, IS_FOLDER_ROLE)) else None
        if old_folder == new_folder:
            return
        old_path_str = item.data(0, DOWNLOAD_PATH_ROLE)
        if not old_path_str:
            return
        old_path = Path(old_path_str)
        if not old_path.is_file():
            return
        new_dir = Path(self._download_dest_dir_for_folder(new_folder, location))
        new_path = new_dir / old_path.name
        try:
            new_dir.mkdir(parents=True, exist_ok=True)
            shutil.move(str(old_path), str(new_path))
        except OSError as exc:
            self._log(f"Couldn't move downloaded file for {item.data(0, URL_ROLE) or ''}: {exc}")
            return
        item.setData(0, DOWNLOAD_PATH_ROLE, str(new_path))
        self._log(f"Moved downloaded file to {new_dir}")

    # Refresh the numbering/prefixes of every item in the tree
    def _renumber_url_list(self):
        order_map = self._subgroup_upload_order_map()
        self._renumber_siblings(None, order_map)
        self._save_links_to_disk()
        self._update_download_button()

    # Re-render row text/colors only (no disk save), used by the per-second retry
    # cooldown tick so a ticking countdown doesn't spam the links file with writes
    def _refresh_url_list_display(self):
        order_map = self._subgroup_upload_order_map()
        self._renumber_siblings(None, order_map)

    # For a Sub Group profile with "Number downloads by upload order" turned on,
    # returns {id(item): rank} for every link currently in the tree (rank 1 = the
    # oldest upload), computed fresh from each link's own UPLOAD_TIMESTAMP_ROLE -
    # never from its position in the tree. Because this is recomputed from scratch
    # every time (on every renumber/probe/download-start) rather than cached, a
    # Refresh reshuffling channels' tree order, or adding new videos partway
    # through, can never leave a stale queue behind - the next call always reflects
    # every link's real upload time as currently known.
    # Returns None for any other profile, or when the setting is off, so callers
    # can fall back to their normal (tree-order) behavior unchanged.
    # A link with no known upload time (e.g. probe hasn't finished, or the site
    # didn't report one) sorts after every link whose upload time IS known, rather
    # than being guessed at - ties (including "unknown vs unknown") keep their
    # current relative tree order.
    def _subgroup_upload_order_map(self):
        profile = self._current_profile_dict()
        if not profile or profile.get("type") != "Sub Group":
            return None
        if not profile.get("number_by_upload_order"):
            return None
        items = [
            it for it in self._iter_all_link_items()
            if not it.data(0, LINK_SKIPPED_ROLE)
            and not it.data(0, LINK_NUMBERING_RESET_ROLE)
        ]
        items.sort(key=lambda it: (
            it.data(0, UPLOAD_TIMESTAMP_ROLE) is None,
            it.data(0, UPLOAD_TIMESTAMP_ROLE) or 0,
        ))
        return {id(it): rank + 1 for rank, it in enumerate(items)}

    # Recursively renumber links and relabel folders under the given parent.
    # order_map, if given (see _subgroup_upload_order_map), overrides each link's
    # displayed number with its precomputed global upload-order rank instead of its
    # position among its own siblings.
    def _renumber_siblings(self, parent_item, order_map=None):
        count = (
            self.url_list.topLevelItemCount()
            if parent_item is None
            else parent_item.childCount()
        )
        number = 1
        for i in range(count):
            child = (
                self.url_list.topLevelItem(i)
                if parent_item is None
                else parent_item.child(i)
            )
            if child.data(0, IS_LOAD_MORE_ROLE):
                continue
            raw = child.data(0, RAW_TEXT_ROLE)
            if child.data(0, IS_FOLDER_ROLE):
                child.setText(0, f"--- {raw}")
            else:
                prefix = "-- " if parent_item is not None else ""
                remaining = child.data(0, DOWNLOAD_TIMEOUT_ROLE)
                if remaining:
                    prefix += f"[{remaining}s] - "
                if child.data(0, FORCE_QUALITY_PENDING_ROLE):
                    prefix += "[Force Quality] "
                if child.data(0, LINK_SKIPPED_ROLE):
                    child.setText(0, f"{prefix}[Skip] - {self._display_text_with_progress(child, raw)}")
                elif child.data(0, LINK_NUMBERING_RESET_ROLE):
                    child.setText(0, f"{prefix}[Done] - {self._display_text_with_progress(child, raw)}")
                else:
                    display_number = (
                        order_map.get(id(child), number) if order_map is not None else number
                    )
                    child.setText(0, f"{prefix}{display_number} - {self._display_text_with_progress(child, raw)}")
                    number += 1
            if child.childCount():
                self._renumber_siblings(child, order_map)

    # Insert "<progress>%" between the quality/size and title portions of a link's raw
    # text, e.g. "1080p 23mb - name" -> "1080p 23mb - 10% - name", once a download has
    # reported progress for it. Left untouched (still just quality/size - title, or the
    # bare URL pre-probe) if no download has ever run for this link.
    def _display_text_with_progress(self, item, raw):
        progress = item.data(0, DOWNLOAD_PROGRESS_ROLE)
        if progress is None or raw == item.data(0, URL_ROLE) or " - " not in raw:
            return raw
        quality_size, title = raw.split(" - ", 1)
        return f"{quality_size} - {progress}% - {title}"

    # Serialize one tree item (and its children, if a folder) into a plain dict
    def _serialize_tree_item(self, item):
        is_folder = bool(item.data(0, IS_FOLDER_ROLE))
        node = {
            "is_folder": is_folder,
            "raw_text": item.data(0, RAW_TEXT_ROLE),
            "disabled": bool(item.data(0, LINK_DISABLED_ROLE)),
            "skipped": bool(item.data(0, LINK_SKIPPED_ROLE)),
            "numbering_reset": bool(item.data(0, LINK_NUMBERING_RESET_ROLE)),
            "expanded": item.isExpanded(),
        }
        if is_folder:
            node["children"] = self._serialize_children(item)
            node["playlist_source_url"] = item.data(0, PLAYLIST_SOURCE_URL_ROLE)
        else:
            node["url"] = item.data(0, URL_ROLE)
            node["uuid"] = item.data(0, LINK_UUID_ROLE) or str(uuid.uuid4())
            node["forced_quality"] = item.data(0, FORCED_QUALITY_ROLE)
            node["probe_failed"] = bool(item.data(0, PROBE_FAILED_ROLE))
            node["members_only"] = bool(item.data(0, MEMBERS_ONLY_ROLE))
            node["channel"] = item.data(0, CHANNEL_ROLE)
            node["upload_date"] = item.data(0, UPLOAD_DATE_ROLE)
            node["upload_timestamp"] = item.data(0, UPLOAD_TIMESTAMP_ROLE)
            node["size"] = item.data(0, SIZE_ROLE)
            node["duration"] = item.data(0, DURATION_ROLE)
            node["title"] = item.data(0, TITLE_ROLE)
            node["download_progress"] = item.data(0, DOWNLOAD_PROGRESS_ROLE)
            node["download_path"] = item.data(0, DOWNLOAD_PATH_ROLE)
            node["playlist_index"] = item.data(0, PLAYLIST_INDEX_ROLE)
        return node

    # Serialize every child of parent (or the top level, if parent is None) into a
    # list of node dicts. A "Load more" sentinel is transparent here: its still-
    # pending raw node dicts are spliced back in as-is instead of the sentinel
    # itself, so saving while a large folder/profile is only partially paginated
    # in never truncates the un-materialized tail.
    def _serialize_children(self, parent):
        count = parent.childCount() if parent is not None else self.url_list.topLevelItemCount()
        result = []
        for i in range(count):
            child = parent.child(i) if parent is not None else self.url_list.topLevelItem(i)
            if child.data(0, IS_LOAD_MORE_ROLE):
                result.extend(child.data(0, LOAD_MORE_NODES_ROLE) or [])
            else:
                result.append(self._serialize_tree_item(child))
        return result

    # Save the current URL/folder tree to disk so it can be restored on next launch
    def _save_links_to_disk(self):
        save_links_file({"items": self._serialize_children(None)})
        self._update_sidebar_info()

    # Recursively yield every link item (not folders) in the tree, or under the
    # given parent folder item if one is passed
    def _iter_all_link_items(self, parent=None):
        count = (
            self.url_list.topLevelItemCount() if parent is None else parent.childCount()
        )
        for i in range(count):
            child = self.url_list.topLevelItem(i) if parent is None else parent.child(i)
            if child.data(0, IS_LOAD_MORE_ROLE):
                continue
            if child.data(0, IS_FOLDER_ROLE):
                yield from self._iter_all_link_items(child)
            else:
                yield child

    # Recompute and display the sidebar's runtime and total-size (enabled,
    # not-yet-completed links only) and total-speed (sum of any in-progress
    # downloads) info lines
    def _update_sidebar_info(self):
        total_bytes = 0
        have_size = False
        total_seconds = 0
        for item in self._iter_all_link_items():
            if item.data(0, LINK_DISABLED_ROLE):
                continue
            if item.data(0, LINK_SKIPPED_ROLE):
                continue
            if item.data(0, DOWNLOAD_PROGRESS_ROLE) == 100:
                continue
            size_bytes = _parse_size_to_bytes(item.data(0, SIZE_ROLE))
            if size_bytes is not None:
                have_size = True
                total_bytes += size_bytes
            duration_seconds = _parse_duration_to_seconds(item.data(0, DURATION_ROLE))
            if duration_seconds is not None:
                total_seconds += duration_seconds
        size_text = _format_size(total_bytes) if have_size else "0mb"
        self.info_label_1.setText(f"Total size: {size_text}")

        total_minutes = total_seconds // 60
        hours, minutes = divmod(total_minutes, 60)
        runtime_text = f"{hours}:{minutes:02d}"
        self.info_label_3.setText(f"Runtime: {runtime_text}")

        total_kbps = sum(self._download_speeds_kbps.values())
        self.info_label_2.setText(f"Speed: {total_kbps:.1f} KB/s")

    # Record (or clear, if kbps is falsy) a link's live download speed in KB/s and
    # refresh the sidebar total; called by the download worker as transfers progress
    def set_download_speed(self, link_uuid, kbps):
        if kbps:
            self._download_speeds_kbps[link_uuid] = kbps
        else:
            self._download_speeds_kbps.pop(link_uuid, None)
        self._update_sidebar_info()

    # Rebuild one tree item (and its children, if a folder) from a saved dict;
    # returns None for malformed entries so a corrupt file can't crash startup
    def _build_tree_item(self, node):
        if not isinstance(node, dict):
            return None
        item = QTreeWidgetItem()
        item.setData(0, RAW_TEXT_ROLE, node.get("raw_text") or "")
        item.setData(0, LINK_DISABLED_ROLE, bool(node.get("disabled")))
        item.setData(0, LINK_SKIPPED_ROLE, bool(node.get("skipped")))
        item.setData(0, LINK_NUMBERING_RESET_ROLE, bool(node.get("numbering_reset")))
        if node.get("is_folder"):
            item.setData(0, IS_FOLDER_ROLE, True)
            playlist_source_url = node.get("playlist_source_url")
            if playlist_source_url:
                item.setData(0, PLAYLIST_SOURCE_URL_ROLE, playlist_source_url)
            self._add_items_batch(item, node.get("children") or [], 0)
        else:
            url = node.get("url")
            # Defense in depth: only ever load genuine http(s) links off disk, even
            # though every normal in-app path that adds a link already goes through
            # _is_valid_url. Without this, a hand-edited or corrupted links.json
            # (or one synced from an untrusted location) could plant a string like
            # "--exec=..." as a "url", which - now that every yt-dlp invocation
            # inserts a "--" before the url argument (see probe_url) - would just be
            # rejected by yt-dlp as an invalid URL rather than silently doing
            # nothing useful, but there's no reason to even hand it to yt-dlp in the
            # first place when it's obviously not a link.
            if not url or not _is_valid_url(url):
                return None
            item.setData(0, URL_ROLE, url)
            link_uuid = node.get("uuid") or str(uuid.uuid4())
            item.setData(0, LINK_UUID_ROLE, link_uuid)
            existing_thumb = _existing_thumbnail_path(link_uuid)
            if existing_thumb is not None:
                item.setData(0, THUMBNAIL_PATH_ROLE, existing_thumb.as_posix())
            if node.get("forced_quality"):
                item.setData(0, FORCED_QUALITY_ROLE, node["forced_quality"])
            item.setData(0, PROBE_FAILED_ROLE, bool(node.get("probe_failed")))
            item.setData(0, MEMBERS_ONLY_ROLE, bool(node.get("members_only")))
            item.setData(0, CHANNEL_ROLE, node.get("channel"))
            item.setData(0, UPLOAD_DATE_ROLE, node.get("upload_date"))
            item.setData(0, UPLOAD_TIMESTAMP_ROLE, node.get("upload_timestamp"))
            item.setData(0, SIZE_ROLE, node.get("size"))
            item.setData(0, DURATION_ROLE, node.get("duration"))
            item.setData(0, TITLE_ROLE, node.get("title"))
            progress = node.get("download_progress")
            if progress is not None:
                item.setData(0, DOWNLOAD_PROGRESS_ROLE, progress)
            download_path = node.get("download_path")
            if download_path:
                item.setData(0, DOWNLOAD_PATH_ROLE, download_path)
            playlist_index = node.get("playlist_index")
            if playlist_index is not None:
                item.setData(0, PLAYLIST_INDEX_ROLE, playlist_index)
        self._apply_item_flags(item)
        item.setExpanded(bool(node.get("expanded")))
        return item

    # Build and attach up to LINKS_LOAD_BATCH_SIZE items from nodes[start_index:] to
    # parent (a folder QTreeWidgetItem, or None for the top level of the tree). If any
    # nodes remain after that, a "Load more" sentinel is appended standing in for them.
    # Returns the list of real (non-sentinel) items actually built.
    def _add_items_batch(self, parent, nodes, start_index):
        end_index = min(start_index + LINKS_LOAD_BATCH_SIZE, len(nodes))
        built = []
        for child_node in nodes[start_index:end_index]:
            child = self._build_tree_item(child_node)
            if child is None:
                continue
            if parent is None:
                self.url_list.addTopLevelItem(child)
            else:
                parent.addChild(child)
            built.append(child)
        remaining = nodes[end_index:]
        if remaining:
            load_more = self._build_load_more_item(remaining)
            if parent is None:
                self.url_list.addTopLevelItem(load_more)
            else:
                parent.addChild(load_more)
        return built

    # Build a non-selectable "Load N more..." row standing in for remaining_nodes
    def _build_load_more_item(self, remaining_nodes):
        item = QTreeWidgetItem()
        item.setData(0, IS_LOAD_MORE_ROLE, True)
        item.setData(0, LOAD_MORE_NODES_ROLE, remaining_nodes)
        batch = min(LINKS_LOAD_BATCH_SIZE, len(remaining_nodes))
        item.setText(0, f"▾ Load {batch} more... ({len(remaining_nodes)} remaining)")
        item.setFlags(Qt.ItemIsEnabled)
        return item

    # Right-click menu for a "Load more" sentinel row: just a "Load all" shortcut
    # that keeps paging until every pending item is materialized
    def _show_load_more_context_menu(self, item, pos):
        menu = QMenu(self)
        menu.setStyleSheet(menu_style())
        act_load_all = menu.addAction("Load all")
        action = menu.exec(self.url_list.mapToGlobal(pos))
        if action == act_load_all:
            self._expand_load_more_all(item)

    # Repeatedly expand a "Load more" sentinel (and whatever fresh sentinel each
    # batch leaves behind) until every one of its pending nodes is materialized
    def _expand_load_more_all(self, item, quiet=False):
        parent = item.parent()
        count = len(item.data(0, LOAD_MORE_NODES_ROLE) or [])
        # This can page through many batches back-to-back on a large list, so a busy
        # cursor covers the whole operation rather than flickering per batch. Nests
        # safely (Qt's override cursor is a stack) with the WaitCursor callers like
        # _on_search_triggered's _materialize_entire_tree already have in place.
        QApplication.setOverrideCursor(Qt.WaitCursor)
        QApplication.processEvents()
        try:
            self._expand_load_more(item)
            while True:
                sentinel = self._find_load_more_sentinel(parent)
                if sentinel is None:
                    break
                self._expand_load_more(sentinel)
                QApplication.processEvents()
        finally:
            QApplication.restoreOverrideCursor()
        if not quiet:
            self._log(f"Loaded {count} more item(s)")

    # The load-more sentinel among parent's children (or the top level, if parent
    # is None), if one is currently present - a folder/level has at most one at a time
    def _find_load_more_sentinel(self, parent):
        count = parent.childCount() if parent is not None else self.url_list.topLevelItemCount()
        for i in range(count):
            child = parent.child(i) if parent is not None else self.url_list.topLevelItem(i)
            if child.data(0, IS_LOAD_MORE_ROLE):
                return child
        return None

    # Fully materialize every "Load more" sentinel anywhere in the tree - top-level
    # and inside every folder, however deeply paginated - so every link becomes a
    # real, selectable QTreeWidgetItem. Used by Search, which needs to be able to
    # find and jump to any link regardless of how much of a large list is still
    # paged out. Cheap to call repeatedly: once nothing's left paginated, it's just
    # a no-op walk of the tree.
    def _materialize_entire_tree(self):
        self._materialize_children(None)

    # Recursively expand every 'load more' placeholder under parent so all its
    # children become real items
    def _materialize_children(self, parent):
        count = parent.childCount() if parent is not None else self.url_list.topLevelItemCount()
        i = 0
        while i < count:
            child = parent.child(i) if parent is not None else self.url_list.topLevelItem(i)
            if child.data(0, IS_LOAD_MORE_ROLE):
                self._expand_load_more_all(child, quiet=True)
                count = parent.childCount() if parent is not None else self.url_list.topLevelItemCount()
                continue
            if child.data(0, IS_FOLDER_ROLE):
                self._materialize_children(child)
            i += 1

    # Handle a click on a "Load more" sentinel row: swap it out for the next batch of
    # real items (plus a fresh sentinel if more remain after that), in place
    def _expand_load_more(self, item):
        nodes = item.data(0, LOAD_MORE_NODES_ROLE) or []
        parent = item.parent()
        if parent is not None:
            parent.removeChild(item)
        else:
            index = self.url_list.indexOfTopLevelItem(item)
            if index != -1:
                self.url_list.takeTopLevelItem(index)
        self._add_items_batch(parent, nodes, 0)
        self._renumber_siblings(parent)
        # The freshly-materialized batch may contain enabled links that weren't
        # visible (and so weren't counted) a moment ago - re-check so the Download
        # button doesn't stay greyed out just because everything *currently built*
        # happened to be disabled or already downloaded.
        self._update_download_button()

    # Load the saved URL/folder tree from disk (if any) and repopulate the tree. Probing is
    # NOT auto-started for restored links - the user retries them manually (e.g. via the
    # context menu) since a restart shouldn't silently kick off a burst of network requests.
    def _load_links_from_disk(self):
        data = load_links_file()
        if not data:
            return
        items = data.get("items")
        if not isinstance(items, list) or not items:
            return
        built = self._add_items_batch(None, items, 0)
        if not built:
            return
        self._renumber_siblings(None)
        if len(items) > len(built):
            self._log(f"Loaded {len(built)} of {len(items)} saved item(s)")
        else:
            self._log(f"Loaded {len(built)} saved item(s)")

    # Build and handle the right-click context menu for the log area
    def _on_log_context_menu(self, pos):
        menu = QMenu(self)
        menu.setStyleSheet(menu_style())
        act_copy = menu.addAction("Copy all")
        act_clear = menu.addAction("Clear")
        menu.addSeparator()
        act_maximize = menu.addAction("Restore" if self._log_maximized else "Maximize")
        action = menu.exec(self.log.mapToGlobal(pos))
        if action == act_copy:
            QApplication.clipboard().setText(self.log.toPlainText())
        elif action == act_clear:
            self._reset_log()
        elif action == act_maximize:
            self._toggle_log_maximized()

    # Show only the log area, or restore the normal split view
    def _toggle_log_maximized(self):
        self._log_maximized = not self._log_maximized
        self.upper_splitter.setVisible(not self._log_maximized)
        self.btn_log_minimize.setVisible(self._log_maximized)
        for widget in (self.btn_settings, self.btn_stop_probing, self.btn_download):
            widget.setVisible(not self._log_maximized)
        if self._log_maximized:
            self.btn_refresh_channel.hide()
        else:
            self._update_refresh_button()

    # Clear the log and rewrite the header line
    def _reset_log(self):
        self.log.setPlainText(self._log_header + "\n")
        self._log_line_cursors.clear()
        self._download_line_blocks.clear()
        self._download_start_blocks.clear()
        if self._ytdlp_update_available:
            self._set_log_header("update available", clickable=True)

    # Rewrite the log's first line - normally "<APP_NAME> v<APP_VERSION> — UI ready"
    # - in place, swapping its "UI ready" tail for suffix. When clickable, the whole
    # line becomes a link to the About settings tab (see _on_log_anchor_clicked), but
    # is deliberately styled to match the surrounding log text exactly (no color or
    # underline) so it doesn't look different from the plain header it replaces.
    def _set_log_header(self, suffix, clickable):
        self._ytdlp_update_available = clickable
        block = self.log.document().findBlockByNumber(0)
        if not block.isValid():
            return
        cursor = QTextCursor(block)
        cursor.select(QTextCursor.SelectionType.LineUnderCursor)
        header_text = f"{APP_NAME} v{APP_VERSION} — {suffix}"
        if clickable:
            cursor.insertHtml(
                f'<a href="ytdlp-update" style="color: {TEXT_SECONDARY}; '
                f'text-decoration: none;">{header_text}</a>'
            )
        else:
            cursor.insertText(header_text)

    # Append a line to the log area
    def _log(self, msg):
        self.log.append(msg)

    # Like _log, but only actually logs when the "Enable detailed log" setting is
    # on - for messages that are useful context but noisy enough to skip by default
    # (e.g. "Moved N item(s) into folder", "Opened folder for N item(s)")
    def _log_detailed(self, msg):
        if self.chk_detailed_log.isChecked():
            self._log(msg)

    # Update (or create) the one live progress line for this download, e.g.
    # "name.webm:  52.8% of   20.74MiB at    2.59MiB/s ETA 00:03" - each call
    # overwrites the same line in place rather than appending a new one per
    # percent tick, for the same reason _append_probe_result_to_log uses a block
    # number instead of a stored cursor (see its comment above).
    def _on_download_line(self, item, text):
        block_number = self._download_line_blocks.get(id(item))
        block = self.log.document().findBlockByNumber(block_number) if block_number is not None else None
        if block is not None and block.isValid():
            cursor = QTextCursor(block)
            cursor.select(QTextCursor.SelectionType.LineUnderCursor)
            cursor.insertText(text)
        else:
            self._log(text)
            self._download_line_blocks[id(item)] = self.log.document().lastBlock().blockNumber()
        self.log.verticalScrollBar().setValue(self.log.verticalScrollBar().maximum())

    # Delete this item's live progress line outright (not just clear its text) once
    # its download finishes, so the log doesn't end up with a stale
    # "|__ 100.0% of 1.90MiB at 3.01MiB/s ETA 00:00" line sitting around once the
    # "Downloading:" line above it has been rewritten to "Completed:" (see
    # _mark_download_log_line_complete).
    def _remove_download_log_line(self, item):
        block_number = self._download_line_blocks.pop(id(item), None)
        if block_number is None:
            return
        block = self.log.document().findBlockByNumber(block_number)
        if not block.isValid():
            return
        cursor = QTextCursor(block)
        cursor.movePosition(QTextCursor.MoveOperation.StartOfBlock)
        next_block = block.next()
        if next_block.isValid():
            # Swallow this block's own trailing separator by reaching into the
            # start of the next block, rather than selecting the block "under" the
            # cursor - which, for a block that's still empty (i.e. never got a
            # single progress tick before the download failed), selects nothing at
            # all, making removeSelectedText() a silent no-op and leaving the
            # blank line behind.
            cursor.setPosition(next_block.position(), QTextCursor.MoveMode.KeepAnchor)
        else:
            # This is the last block in the log - there's no following separator to
            # reach into, so reach backward and swallow the separator before it
            # instead.
            cursor.movePosition(QTextCursor.MoveOperation.PreviousBlock, QTextCursor.MoveMode.KeepAnchor)
            cursor.movePosition(QTextCursor.MoveOperation.EndOfBlock, QTextCursor.MoveMode.KeepAnchor)
        cursor.removeSelectedText()

    # Rewrite this item's own "Downloading: <name>" line into "Completed: <name>"
    # in place, rather than leaving that line as-is and logging a whole separate
    # "Downloaded: ..." line underneath it - one line per download instead of two
    # keeps the log a lot shorter once several items have finished. Falls back to
    # a normal new log line if that block's gone missing for some reason (e.g. the
    # log was cleared mid-download).
    def _mark_download_log_line_complete(self, item, name):
        block_number = self._download_start_blocks.pop(id(item), None)
        block = self.log.document().findBlockByNumber(block_number) if block_number is not None else None
        if block is not None and block.isValid():
            cursor = QTextCursor(block)
            cursor.select(QTextCursor.SelectionType.LineUnderCursor)
            cursor.insertText(f"Completed: {name}")
        else:
            self._log(f"Completed: {name}")

    # Log "URL added: <url>" and remember which block (line) it landed on so the
    # probe result can be appended to it later instead of starting a new line.
    # A live QTextCursor isn't safe to store here: Qt pushes a cursor forward
    # whenever new text is inserted right at its position, so a cursor saved at
    # "end of this line" drifts to "end of the next line" as soon as the next
    # URL is logged. A block number doesn't have that problem.
    def _log_url_added(self, item, url):
        self._log(f"URL added: {url}")
        self._log_line_cursors[id(item)] = self.log.document().lastBlock().blockNumber()

    # Append " → <title>" onto a link's existing log line; logs a new line if that
    # line can no longer be found (e.g. the log was cleared in the meantime)
    def _append_probe_result_to_log(self, item, title):
        block_number = self._log_line_cursors.pop(id(item), None)
        block = self.log.document().findBlockByNumber(block_number) if block_number is not None else None
        if block is None or not block.isValid():
            self._log(f"Probed → {title}")
            return
        cursor = QTextCursor(block)
        cursor.movePosition(QTextCursor.MoveOperation.EndOfBlock)
        cursor.insertText(f" → {title}")
        self.log.verticalScrollBar().setValue(self.log.verticalScrollBar().maximum())


    # Enable or disable the proxy host/port fields based on the checkbox
    def _on_proxy_toggled(self, state):
        enabled = bool(state)
        self.proxy_host_edit.setEnabled(enabled)
        self.proxy_port_spin.setEnabled(enabled)

    # Enable or disable the scheduler's start-time field based on its checkbox
    def _on_scheduler_start_toggled(self, state):
        self.scheduler_start_time_edit.setEnabled(bool(state))
        self._update_status_label()

    # Enable or disable the scheduler's stop-time field based on its checkbox
    def _on_scheduler_stop_toggled(self, state):
        self.scheduler_stop_time_edit.setEnabled(bool(state))
        self._update_settings_sidebar_info()

    # Resize the download thread pool to match the "Parallel downloads" setting
    def _on_parallel_downloads_changed(self, value):
        self._download_pool.setMaxThreadCount(value)

    # Sort key for the profile list: Default always first, then every other profile
    # alphabetically by type and, within a type, alphabetically by name.
    def _profile_sort_key(self, profile):
        if profile["name"] == DEFAULT_PROFILE_NAME:
            return (0, "", "")
        return (1, (profile.get("type") or "").lower(), profile["name"].lower())

    # Repopulate the profile list widget from the in-memory registry, selecting
    # whichever profile is currently active. Sorted with Default pinned on top,
    # then everything else alphabetically by type and then by name, labelled
    # "type - name" (just "default" for the Default profile, which has no type).
    # A non-selectable separator row is inserted between each type's group (and
    # between Default and whatever follows it) so the grouping is visible at a
    # glance rather than just implied by the alphabetical sort.
    def _reload_profile_list(self):
        self.profile_list.clear()
        previous_group = None
        for profile in sorted(self._profiles, key=self._profile_sort_key):
            name = profile["name"]
            if name == DEFAULT_PROFILE_NAME:
                label = "default"
                group = ""
            else:
                ptype = profile.get("type")
                label = f"{ptype.lower()} - {name}" if ptype else name
                group = ptype or ""
            if previous_group is not None and group != previous_group:
                self._add_profile_list_separator()
            previous_group = group
            item = QListWidgetItem(label)
            item.setData(Qt.UserRole, name)
            self.profile_list.addItem(item)
            if name == self._current_profile_name:
                self.profile_list.setCurrentItem(item)
        self.btn_delete_profile.setEnabled(len(self._profiles) > 1)
        self._resize_list_to_contents(self.profile_list)

    # Add a non-selectable, non-clickable divider row to the profile list, used by
    # _reload_profile_list to visually split one profile-type group from the next.
    # Just a flagged, empty item - _ProfileListSeparatorDelegate (set as
    # profile_list's item delegate) does the actual painting of a full-width,
    # vertically-centered line for it.
    def _add_profile_list_separator(self):
        item = QListWidgetItem()
        item.setFlags(Qt.NoItemFlags)
        item.setData(PROFILE_LIST_SEPARATOR_ROLE, True)
        item.setSizeHint(QSize(0, 11))
        self.profile_list.addItem(item)

    # Show/hide the "Channels in this sub group" list and its Add/Remove buttons
    # depending on whether the active profile is a "Sub Group" - and if it is,
    # repopulate the list from its current channels.
    def _update_subgroup_channels_visibility(self):
        profile = self._current_profile_dict()
        is_subgroup = bool(profile and profile.get("type") == "Sub Group")
        self.subgroup_channels_label.setVisible(is_subgroup)
        self.subgroup_channel_list.setVisible(is_subgroup)
        self.subgroup_channel_button_row.setVisible(is_subgroup)
        self.chk_subgroup_number_by_upload_order.setVisible(is_subgroup)
        if is_subgroup:
            self._reload_subgroup_channel_list()
            self.chk_subgroup_number_by_upload_order.blockSignals(True)
            self.chk_subgroup_number_by_upload_order.setChecked(
                bool(profile.get("number_by_upload_order"))
            )
            self.chk_subgroup_number_by_upload_order.blockSignals(False)

    # Repopulate the Sub Group channel list from the active profile's own
    # "channels" metadata (each shown as "name — url")
    def _reload_subgroup_channel_list(self):
        self.subgroup_channel_list.clear()
        profile = self._current_profile_dict()
        channels = (profile.get("channels") or []) if profile else []
        for channel in channels:
            item = QListWidgetItem(f"{channel.get('name')} — {channel.get('url')}")
            item.setData(Qt.UserRole, channel.get("name"))
            self.subgroup_channel_list.addItem(item)
        self._resize_list_to_contents(self.subgroup_channel_list)

    # "Number downloads by upload order" checkbox (Sub Group profiles only):
    # persist the flag onto the active profile and immediately re-render the tree's
    # numbering to match, so the effect is visible without needing a Refresh.
    def _on_subgroup_number_by_upload_order_toggled(self, checked):
        profile = self._current_profile_dict()
        if not profile or profile.get("type") != "Sub Group":
            return
        profile["number_by_upload_order"] = checked
        save_profile_metadata(
            profile["name"], profile.get("type"), profile.get("channel_url"),
            profile.get("channels"), checked,
        )
        self._renumber_url_list()

    # "Add Channel..." button (Sub Group profiles only): prompt for a channel name
    # (doubles as its own sidebar folder name) and its "/videos" or "/shorts" link,
    # append it to the profile's channels, persist, and create its (empty, until the
    # next Refresh) tracking folder right away.
    def _on_add_channel_clicked(self):
        profile = self._current_profile_dict()
        if not profile or profile.get("type") != "Sub Group":
            return
        channels = profile.get("channels") or []

        name, ok = QInputDialog.getText(
            self, "Add Channel", "Channel name (used as its sidebar folder name):"
        )
        if not ok:
            return
        name = name.strip()
        if not name:
            self._log("Add channel: enter a valid name")
            return
        if any(c.get("name") == name for c in channels):
            self._log(f"Add channel: '{name}' already exists in this sub group")
            return

        url, ok = QInputDialog.getText(
            self, "Add Channel",
            "Channel videos or shorts link (e.g. https://www.youtube.com/@name/videos "
            "or @name/shorts):",
        )
        if not ok:
            return
        url = url.strip()
        if not _is_channel_videos_url(url):
            self._log(
                "Add channel: channel link must be a channel's \"/videos\" or \"/shorts\" page, "
                "e.g. https://www.youtube.com/@name/videos"
            )
            return

        channels = channels + [{"name": name, "url": url, "quality": self.quality_combo.currentText()}]
        profile["channels"] = channels
        save_profile_metadata(
            profile["name"], profile.get("type"), profile.get("channel_url"), channels,
            profile.get("number_by_upload_order"),
        )
        folder = self._get_or_create_named_folder(name)
        folder.setData(0, FOLDER_QUALITY_ROLE, self.quality_combo.currentText())
        self._renumber_url_list()
        self._reload_subgroup_channel_list()
        self._update_refresh_button()
        self._update_url_line_edit_for_profile()
        self._log(f"Added channel '{name}' to sub group '{profile['name']}'")

    # "Remove Channel" button (Sub Group profiles only): drop the selected channel
    # from the profile's metadata and remove its tracking folder (and, optionally,
    # its downloaded files) from the tree - so a future Refresh doesn't bring it
    # back.
    def _on_remove_channel_clicked(self):
        profile = self._current_profile_dict()
        if not profile or profile.get("type") != "Sub Group":
            return
        selected = self.subgroup_channel_list.selectedItems()
        if not selected:
            self._log("Remove channel: select a channel first")
            return
        name = selected[0].data(Qt.UserRole)

        delete_from_disk = self._confirm_removal(
            f"Remove channel '{name}' from this sub group? Its sidebar folder and "
            "tracked links will be removed too.",
            title="Remove Channel",
            checkbox_label="Also delete its downloaded files from disk",
        )
        if delete_from_disk is None:
            return

        channels = [c for c in (profile.get("channels") or []) if c.get("name") != name]
        profile["channels"] = channels
        save_profile_metadata(
            profile["name"], profile.get("type"), profile.get("channel_url"), channels,
            profile.get("number_by_upload_order"),
        )

        folder = self._find_folder_by_name(name)
        if folder is not None:
            self._cancel_probes_for_item(folder)
            self._cancel_download_for_item(folder)
            for link_uuid in self._collect_link_uuids(folder):
                remove_thumbnail(link_uuid)
            if delete_from_disk:
                self._delete_files_from_disk(folder)
            index = self._sibling_index(None, folder)
            if index != -1:
                self._take_sibling(None, index)
            self._renumber_url_list()

        self._reload_subgroup_channel_list()
        self._update_refresh_button()
        suffix = " and deleted its downloaded files" if delete_from_disk else ""
        self._log(f"Removed channel '{name}' from sub group{suffix}")

    # Build and handle the right-click context menu for the profile list
    def _on_profile_list_context_menu(self, pos):
        selected = self.profile_list.selectedItems()
        if not selected:
            return
        name = selected[0].data(Qt.UserRole)
        menu = QMenu(self)
        menu.setStyleSheet(menu_style())
        act_switch = menu.addAction("Switch to")
        act_switch.setEnabled(name != self._current_profile_name)
        act_delete = menu.addAction("Delete")
        act_delete.setEnabled(len(self._profiles) > 1 and name != DEFAULT_PROFILE_NAME)
        action = menu.exec(self.profile_list.viewport().mapToGlobal(pos))
        if action == act_switch:
            self.profile_combo.setCurrentText(name)
        elif action == act_delete:
            self._delete_profile(name)

    # Refresh the Plugins tab list from self._enabled_plugins. Any plugin whose
    # file has since gone missing or no longer starts with the marker comment is
    # shown in the failed-probe color, as a hint something needs attention.
    def _reload_plugin_list(self):
        self.plugin_list.clear()
        plugins_dir = _plugins_dir()
        for name in self._enabled_plugins:
            item = QListWidgetItem(name)
            item.setData(Qt.UserRole, name)
            candidate = plugins_dir / name
            if not (candidate.is_file() and _is_valid_plugin_file(candidate)):
                item.setForeground(QColor(PROBE_FAILED_COLOR))
            self.plugin_list.addItem(item)

    # "Browse..." button: only accepts a .py file from inside plugins/ whose
    # first line is the PLUGIN_MARKER_COMMENT
    def _on_browse_plugin_clicked(self):
        plugins_dir = _plugins_dir()
        try:
            plugins_dir.mkdir(parents=True, exist_ok=True)
        except OSError:
            pass
        file_path, _ = QFileDialog.getOpenFileName(
            self, "Add Plugin", str(plugins_dir), "Python files (*.py)"
        )
        if not file_path:
            return

        chosen = Path(file_path).resolve()
        try:
            chosen.relative_to(plugins_dir.resolve())
        except ValueError:
            QMessageBox.warning(
                self, "Invalid plugin location",
                f'Plugins can only be added from inside the "{PLUGINS_DIRNAME}" folder.',
            )
            return

        if not _is_valid_plugin_file(chosen):
            QMessageBox.warning(
                self, "Invalid plugin",
                "This file isn't recognized as a plugin - its first line must be "
                f"the comment '{PLUGIN_MARKER_COMMENT}'.",
            )
            return

        name = chosen.name
        if name in self._enabled_plugins:
            QMessageBox.information(self, "Already added", f'"{name}" is already in the plugin list.')
            return

        self._enabled_plugins.append(name)
        save_enabled_plugins(self._enabled_plugins)
        self._reload_plugin_list()

    # Build and handle the right-click context menu for the plugin list
    def _on_plugin_list_context_menu(self, pos):
        selected = self.plugin_list.selectedItems()
        if not selected:
            return
        name = selected[0].data(Qt.UserRole)
        menu = QMenu(self)
        menu.setStyleSheet(menu_style())
        act_remove = menu.addAction("Remove")
        action = menu.exec(self.plugin_list.viewport().mapToGlobal(pos))
        if action == act_remove and name in self._enabled_plugins:
            self._enabled_plugins.remove(name)
            save_enabled_plugins(self._enabled_plugins)
            self._reload_plugin_list()

    # React to the profile combo box changing (either the user picking a different
    # profile, or a New Profile creation setting it to the freshly-added one)
    def _on_profile_combo_changed(self, text):
        if text and text != self._current_profile_name:
            self._switch_profile(text)
            self._reload_profile_list()

    # "New..." button: ask for a name, then a type, then create and switch to it
    def _on_new_profile_clicked(self):
        name, ok = QInputDialog.getText(self, "New Profile", "Profile name:")
        if not ok:
            return
        name = _sanitize_profile_name(name.strip())
        if not name:
            self._log("New profile: enter a valid name")
            return
        if any(p["name"].lower() == name.lower() for p in self._profiles):
            self._log(f"New profile: '{name}' already exists")
            return
        ptype, ok = QInputDialog.getItem(
            self, "New Profile", "Profile type:", PROFILE_TYPES, 0, False
        )
        if not ok:
            return
        channel_url = None
        channels = None
        if ptype == "Channel":
            channel_url, ok = QInputDialog.getText(
                self, "New Profile",
                "Channel videos or shorts link (e.g. https://www.youtube.com/@name/videos "
                "or @name/shorts):",
            )
            if not ok:
                return
            channel_url = channel_url.strip()
            if not _is_channel_videos_url(channel_url):
                self._log(
                    "New profile: channel link must be a channel's \"/videos\" or \"/shorts\" page, "
                    "e.g. https://www.youtube.com/@name/videos"
                )
                return
        elif ptype == "Sub Group":
            channels = self._prompt_new_subgroup_channels()
            if not channels:
                return
        self._profiles.append({
            "name": name, "type": ptype, "channel_url": channel_url, "channels": channels,
            "number_by_upload_order": False,
        })
        save_profile_metadata(name, ptype, channel_url, channels)
        self.profile_combo.blockSignals(True)
        self.profile_combo.addItem(name)
        self.profile_combo.blockSignals(False)
        self._reload_profile_list()
        self._log(f"Created profile '{name}' ({ptype})")
        self.profile_combo.setCurrentText(name)

    # Collects one or more {"name","url"} channel entries for a new "Sub Group"
    # profile: each channel needs a unique name (used as its own sidebar folder
    # name) and a valid "/videos" or "/shorts" link, same as a plain Channel
    # profile's own link. Returns None if the user backs out before adding any
    # channel, otherwise the list of channels collected.
    def _prompt_new_subgroup_channels(self):
        channels = []
        while True:
            prompt = (
                "Channel name (used as its sidebar folder name):" if not channels
                else f"Channel name ({len(channels)} added so far) - another channel:"
            )
            name, ok = QInputDialog.getText(self, "New Sub Group", prompt)
            if not ok:
                return channels or None
            name = name.strip()
            if not name:
                self._log("New profile: enter a valid channel name")
                continue
            if any(c["name"] == name for c in channels):
                self._log(f"New profile: '{name}' was already added")
                continue

            url, ok = QInputDialog.getText(
                self, "New Sub Group",
                f"'{name}' channel videos or shorts link (e.g. https://www.youtube.com/@name/videos "
                "or @name/shorts):",
            )
            if not ok:
                return channels or None
            url = url.strip()
            if not _is_channel_videos_url(url):
                self._log(
                    "New profile: channel link must be a channel's \"/videos\" or \"/shorts\" page, "
                    "e.g. https://www.youtube.com/@name/videos"
                )
                continue

            channels.append({"name": name, "url": url, "quality": self.quality_combo.currentText()})
            cont = QMessageBox.question(
                self, "New Sub Group", "Add another channel?",
                QMessageBox.Yes | QMessageBox.No, QMessageBox.Yes,
            )
            if cont != QMessageBox.Yes:
                return channels

    # "Delete" button: delete whichever profile is selected in the list (or the
    # active one if none is selected)
    def _on_delete_profile_clicked(self):
        selected = self.profile_list.selectedItems()
        name = selected[0].data(Qt.UserRole) if selected else self._current_profile_name
        self._delete_profile(name)

    # Remove a profile from the registry and delete its folder (links/settings/
    # thumbnails) from disk. Switches away first if the deleted profile was active.
    def _delete_profile(self, name):
        if name == DEFAULT_PROFILE_NAME:
            self._log("The Default profile can't be deleted")
            return
        if len(self._profiles) <= 1:
            return
        delete_from_disk = self._confirm_removal(
            f"Delete profile '{name}' and all its saved links, settings, and "
            "thumbnails? This cannot be undone.",
            title="Delete Profile",
            checkbox_label="Also delete downloaded files from disk",
        )
        if delete_from_disk is None:
            return
        if delete_from_disk:
            links_data = _load_json_file(_dir_for_profile(name) / LINKS_FILENAME) or {}
            for path_str in _collect_download_paths_from_nodes(links_data.get("items") or []):
                path = Path(path_str)
                try:
                    if path.exists():
                        path.unlink()
                except OSError as e:
                    self._log(f"Failed to delete file from disk: {path} ({e})")
        switching_away = name == self._current_profile_name
        self._profiles = [p for p in self._profiles if p["name"] != name]
        if switching_away:
            self._switch_profile(self._profiles[0]["name"])
        shutil.rmtree(_dir_for_profile(name), ignore_errors=True)
        self.profile_combo.blockSignals(True)
        self.profile_combo.clear()
        self.profile_combo.addItems([p["name"] for p in self._profiles])
        self.profile_combo.setCurrentText(self._current_profile_name)
        self.profile_combo.blockSignals(False)
        self._reload_profile_list()
        suffix = " and deleted its downloaded files" if delete_from_disk else ""
        self._log(f"Deleted profile '{name}'{suffix}")


    # Re-apply setStyleSheet() to every widget so it picks up the theme's colors
    def _refresh_theme_styles(self):
        self.central.setStyleSheet(f"background-color: {BG_WINDOW};")
        self.log.setStyleSheet(log_style())
        self.log.viewport().setStyleSheet(f"background-color: {BG_LOG};")
        self.log_container.setStyleSheet(panel_style())
        self.main_splitter.setStyleSheet(splitter_handle_style())
        self.upper_splitter.setStyleSheet(splitter_handle_style())
        self.left_widget.setStyleSheet(panel_style())
        self.url_list.setStyleSheet(url_list_style())

        self.settings_tab_bar.setStyleSheet(panel_style())
        self.settings_body_separator_line.setStyleSheet(f"background-color: {BORDER_DISABLED}; border: none;")
        self.connection_separator_line.setStyleSheet(f"background-color: {BORDER_DISABLED}; border: none;")
        self.general_separator_line.setStyleSheet(f"background-color: {BORDER_DISABLED}; border: none;")

        for label in self._form_labels:
            label.setStyleSheet(sidebar_label_muted_style())

        for combo in (self.quality_combo, self.profile_combo):
            combo.setStyleSheet(settings_input_style())
        self.proxy_port_spin.setStyleSheet(settings_input_style())
        for spin in (self.parallel_downloads_spin, self.probing_timeout_spin, self.retry_count_spin):
            spin.setStyleSheet(settings_input_style())
        self.location_edit.setStyleSheet(settings_input_style())
        self.proxy_host_edit.setStyleSheet(settings_input_style())
        self.ignore_title_pattern_edit.setStyleSheet(settings_input_style())
        for time_edit in (self.scheduler_start_time_edit, self.scheduler_stop_time_edit):
            time_edit.setStyleSheet(settings_input_style())
        for btn in (
            self.btn_browse_location, self.btn_new_profile, self.btn_delete_profile,
        ):
            btn.setStyleSheet(button_style())
        for chk in (
            self.chk_proxy, self.chk_detailed_log, self.chk_number_playlist_downloads,
            self.chk_scheduler_start, self.chk_scheduler_stop,
        ):
            chk.setStyleSheet(checkbox_style())
        self.profile_list.setStyleSheet(profile_list_style())
        self._reload_profile_list()
        self.plugins_note_label.setStyleSheet(sidebar_label_muted_style())

        self.about_name_label.setStyleSheet(f"color: {TEXT_PRIMARY}; font-size: 16px; font-weight: bold;")
        self.about_description_label.setStyleSheet(sidebar_label_muted_style())
        self.about_separator_line.setStyleSheet(f"background-color: {BORDER_DISABLED}; border: none;")
        self.about_version_label.setStyleSheet(sidebar_label_muted_style())
        self.about_app_update_text_label.setStyleSheet(sidebar_label_muted_style())
        self.about_app_update_link_label.setStyleSheet(
            f"color: {BORDER_FOCUS}; font-size: 11px; text-decoration: underline;"
        )
        self.about_ytdlp_version_label.setStyleSheet(sidebar_label_muted_style())
        self.about_ytdlp_update_text_label.setStyleSheet(sidebar_label_muted_style())
        self.about_ytdlp_update_link_label.setStyleSheet(
            f"color: {BORDER_FOCUS}; font-size: 11px; text-decoration: underline;"
        )
        self.about_ffmpeg_version_label.setStyleSheet(sidebar_label_muted_style())
        self.about_ffmpeg_update_text_label.setStyleSheet(sidebar_label_muted_style())
        self.about_ffmpeg_update_link_label.setStyleSheet(
            f"color: {BORDER_FOCUS}; font-size: 11px; text-decoration: underline;"
        )
        for value_edit, copy_btn in self._donate_row_widgets:
            value_edit.setStyleSheet(settings_input_style())
            copy_btn.setStyleSheet(button_style())

        self.url_widget.setStyleSheet(panel_style())
        self.url_line_edit.setStyleSheet(line_edit_style())

        self.sidebar_scroll.setStyleSheet(panel_style())
        self.sidebar_scroll.viewport().setStyleSheet(f"background-color: {BG_PANEL}; border: none;")
        self.settings_sidebar_content.setStyleSheet(panel_style())
        self.settings_sidebar_label.setStyleSheet(f"color: {TEXT_PRIMARY}; font-size: 14px; font-weight: bold;")
        self.settings_sidebar_separator.setStyleSheet(separator_style(margin_top=10))
        for label in (
            self.settings_status_label, self.settings_profile_label, self.settings_quality_label,
            self.settings_proxy_label, self.settings_scheduler_label, self.settings_update_label,
        ):
            label.setStyleSheet(sidebar_label_muted_style())
        self.name_label.setStyleSheet(f"color: {TEXT_PRIMARY}; font-size: 14px; font-weight: bold;")
        self.profile_label.setStyleSheet(sidebar_label_muted_style())
        self.status_label.setStyleSheet(sidebar_label_muted_style())
        self.separator.setStyleSheet(separator_style(margin_top=10))
        self.info_label_1.setStyleSheet(sidebar_label_muted_style())
        self.info_label_2.setStyleSheet(sidebar_label_muted_style())
        self.info_label_3.setStyleSheet(sidebar_label_muted_style())
        self.session_status_label.setStyleSheet(sidebar_label_muted_style())
        self.preview_label.setStyleSheet(
            f"background-color: {BG_THUMBNAIL}; border: 1px solid {BORDER_THUMBNAIL}; color: {TEXT_FAINT};"
        )
        self.settings_sidebar_preview_label.setStyleSheet(
            f"background-color: {BG_THUMBNAIL}; border: 1px solid {BORDER_THUMBNAIL}; color: {TEXT_FAINT};"
        )
        self.title_label.setStyleSheet(f"color: {TEXT_PRIMARY}; font-weight: bold; font-size: 12px;")
        self.subtitle_label.setStyleSheet(f"color: {TEXT_SECONDARY}; font-size: 10px;")
        self.detail_label.setStyleSheet(f"color: {TEXT_MUTED}; font-size: 10px;")
        self.duration_label.setStyleSheet(f"color: {TEXT_MUTED}; font-size: 10px;")
        self.btn_settings.set_active(self.left_stack.currentIndex() == 1)

        if self._settings_search_highlight is not None:
            self._settings_search_highlight_original = self._settings_search_highlight.styleSheet()
            self._settings_search_highlight.setStyleSheet(settings_search_highlight_style())

        app = QApplication.instance()
        if app is not None:
            apply_scrollbar_style(app)


# Application entry point: configure the Qt app and show the main window
def main():
    # On Windows, the taskbar icon (unlike the title-bar icon) isn't taken from
    # QApplication.setWindowIcon() - it's taken from the process's AppUserModelID
    # (AUMID), which groups windows in the taskbar. Without setting one explicitly,
    # a script run via python.exe/pythonw.exe (or an unpackaged frozen exe with no
    # AUMID) gets grouped under Python's own AUMID, so Windows shows Python's
    # generic icon in the taskbar even though app.setWindowIcon() below correctly
    # sets the title bar icon. Must run before QApplication() is constructed.
    if sys.platform == "win32":
        import ctypes
        try:
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(
                "ytdlp-links.app.1.0"
            )
        except Exception:
            pass
    app = QApplication(sys.argv)
    # Only one instance of the app should ever run at once - if another is already
    # running, hand off to it (raising/focusing its window) and quit immediately
    # rather than opening a second one alongside it.
    if _try_activate_running_instance():
        return
    app.setStyle("Fusion")
    app.setEffectEnabled(Qt.UIEffect.UI_AnimateCombo, False)
    # Makes sure this app's persistent ytdlp-bin folder exists so the startup
    # missing-binaries check, the About tab, and any download/probe all agree on
    # where to look - see _bundled_bin_dir. Doesn't create the binaries
    # themselves; see _check_required_binaries_on_startup for that.
    _bundled_bin_dir()
    # Sets the icon used for the window's title bar/taskbar entry (and, packaged as
    # a real .exe via PyInstaller with this same icon.png passed to its --icon flag,
    # the executable's own file icon too - that part isn't something the running
    # app can control, only the build step that produces the .exe). Silently skips
    # a missing/invalid file rather than failing to start the app over a cosmetic
    # icon.
    icon_path = _app_icon_path()
    if icon_path.is_file():
        icon = QIcon(str(icon_path))
        if not icon.isNull():
            app.setWindowIcon(icon)
    win = MainWindow()
    # Belt-and-suspenders: QApplication.setWindowIcon() above is supposed to
    # propagate to every top-level window automatically, and it does for the
    # title-bar icon - but on Windows the *taskbar* button's icon (set via
    # WM_SETICON on the native HWND) doesn't reliably pick up the inherited
    # app icon the moment the very first top-level window is created/shown.
    # That's what caused the taskbar to show a generic icon until some other
    # top-level window (e.g. a QMessageBox from a profile switch) got created
    # and made Windows re-associate the taskbar group's icon. Setting the
    # icon explicitly on the window itself avoids relying on that inheritance
    # timing.
    if icon_path.is_file() and not icon.isNull():
        win.setWindowIcon(icon)
    # Kept alive for as long as the window is (i.e. the app's whole lifetime) so
    # the socket keeps listening - see _listen_for_other_instances.
    win._instance_server = _listen_for_other_instances(win)
    win.show()
    # See _force_windows_taskbar_icon's docstring/comment: this fixes the
    # taskbar button showing a generic icon on first launch, which the
    # earlier app.setWindowIcon()/win.setWindowIcon() calls above don't
    # reliably do on their own. Needs a real HWND, hence called after show().
    _force_windows_taskbar_icon(win)
    # Checked once per launch, after the window's up: this app no longer ships
    # yt-dlp/ffmpeg inside the .exe (see _bundled_bin_dir), so a fresh install has
    # neither yet - see _check_required_binaries_on_startup.
    win._check_required_binaries_on_startup()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()