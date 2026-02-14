/**
 * @file trit_gui.h
 * @brief Trit Linux — Ternary GUI Framework Header
 *
 * Minimal Wayland-like compositor using ternary graphics primitives.
 * Provides a framebuffer interface, ternary color model ({-1,0,+1}
 * for R/G/B with NDR blending), window management with trit-priority
 * stacking, and basic input event handling.
 *
 * Enhancement 3 from LOGICAL_ENHANCEMENTS_FOR_TRIT_LINUX.md:
 *   "Graphical User Interface (GUI) and Display Drivers"
 *
 * Key features:
 *   - Ternary framebuffer: 81x27 trit pixels (2187 total)
 *   - Trit color model: {-1,0,+1} per R/G/B channel (27 colors)
 *   - Window manager with trit-priority stacking (+1=top)
 *   - Basic drawing primitives (pixel, line, rect, fill)
 *   - Input event queue (keyboard + mouse analogs)
 *   - TWTM-accelerated matrix ops for rendering
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef TRIT_LINUX_TRIT_GUI_H
#define TRIT_LINUX_TRIT_GUI_H

#include "set5/trit.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Display Constants ================================================= */

#define TGUI_FB_WIDTH        81    /* 3^4 = 81 trit pixels wide            */
#define TGUI_FB_HEIGHT       27    /* 3^3 = 27 trit pixels tall            */
#define TGUI_FB_PIXELS       (TGUI_FB_WIDTH * TGUI_FB_HEIGHT)
#define TGUI_MAX_WINDOWS     9     /* 3^2 = 9 windows max                  */
#define TGUI_MAX_EVENTS      32    /* Event queue depth                    */
#define TGUI_TITLE_LEN       24    /* Max window title length              */

/* ==== Color Model ======================================================= */

/**
 * @brief Ternary pixel color: {-1, 0, +1} per R/G/B channel.
 *
 * 27 possible colors (3^3). NDR (Non-Destructive Read) blending:
 * blend(a,b) = trit_or(a,b) per channel.
 *
 * Examples:
 *   Black   = {-1, -1, -1}
 *   White   = {+1, +1, +1}
 *   Red     = {+1, -1, -1}
 *   Green   = {-1, +1, -1}
 *   Blue    = {-1, -1, +1}
 *   Gray    = { 0,  0,  0}  (Unknown = neutral)
 */
typedef struct {
    trit r;   /**< Red channel:   -1=off, 0=half, +1=full */
    trit g;   /**< Green channel: -1=off, 0=half, +1=full */
    trit b;   /**< Blue channel:  -1=off, 0=half, +1=full */
} tgui_color_t;

/* Predefined colors */
#define TGUI_COLOR_BLACK   ((tgui_color_t){-1, -1, -1})
#define TGUI_COLOR_WHITE   ((tgui_color_t){ 1,  1,  1})
#define TGUI_COLOR_RED     ((tgui_color_t){ 1, -1, -1})
#define TGUI_COLOR_GREEN   ((tgui_color_t){-1,  1, -1})
#define TGUI_COLOR_BLUE    ((tgui_color_t){-1, -1,  1})
#define TGUI_COLOR_GRAY    ((tgui_color_t){ 0,  0,  0})
#define TGUI_COLOR_YELLOW  ((tgui_color_t){ 1,  1, -1})
#define TGUI_COLOR_CYAN    ((tgui_color_t){-1,  1,  1})
#define TGUI_COLOR_MAGENTA ((tgui_color_t){ 1, -1,  1})

/* ==== Input Events ====================================================== */

/** Input event types */
typedef enum {
    TGUI_EVT_NONE     = 0,
    TGUI_EVT_KEY_DOWN = 1,
    TGUI_EVT_KEY_UP   = 2,
    TGUI_EVT_MOUSE_MOVE = 3,
    TGUI_EVT_MOUSE_CLICK = 4
} tgui_event_type_t;

/** Input event */
typedef struct {
    tgui_event_type_t type;
    int               key_code;  /**< Key code (for keyboard events)      */
    int               x, y;      /**< Coordinates (for mouse events)      */
    int               window_id; /**< Target window (-1 = global)         */
} tgui_event_t;

/* ==== Window ============================================================ */

/**
 * @brief GUI window with trit-priority stacking.
 *
 * Priority maps to trit:
 *   +1 = foreground (topmost)
 *    0 = normal
 *   -1 = background (bottom)
 */
typedef struct {
    int           id;                    /**< Window ID (0-based)           */
    char          title[TGUI_TITLE_LEN]; /**< Window title                  */
    int           x, y;                  /**< Position in framebuffer       */
    int           width, height;         /**< Dimensions                    */
    trit          priority;              /**< Stacking priority             */
    tgui_color_t  bg_color;              /**< Background color              */
    int           visible;               /**< 1 = visible, 0 = hidden       */
    int           dirty;                 /**< 1 = needs redraw              */

    /* Window content buffer (local framebuffer region) */
    tgui_color_t  content[TGUI_FB_WIDTH * TGUI_FB_HEIGHT];
    int           content_width;
    int           content_height;
} tgui_window_t;

/* ==== Compositor State ================================================== */

/**
 * @brief GUI compositor state.
 *
 * Manages the global framebuffer, window list, and event queue.
 * Composites windows by trit-priority: +1 drawn last (on top).
 */
typedef struct {
    tgui_color_t   framebuffer[TGUI_FB_PIXELS]; /**< Display framebuffer  */
    tgui_window_t  windows[TGUI_MAX_WINDOWS];   /**< Window table         */
    int            window_count;     /**< Active windows                    */
    int            initialized;      /**< 1 = compositor ready              */

    /* Event queue (ring buffer) */
    tgui_event_t   events[TGUI_MAX_EVENTS];
    int            evt_head, evt_tail, evt_count;

    /* Statistics */
    int            frames_rendered;  /**< Total frames composited           */
    int            pixels_drawn;     /**< Total pixels written              */
    int            events_processed; /**< Total events handled              */
} tgui_compositor_t;

/* ==== Initialization ==================================================== */

/** Initialize the GUI compositor */
int tgui_init(tgui_compositor_t *comp);

/* ==== Framebuffer Operations ============================================ */

/** Clear framebuffer to a solid color */
void tgui_clear(tgui_compositor_t *comp, tgui_color_t color);

/** Set a single pixel */
int tgui_set_pixel(tgui_compositor_t *comp, int x, int y, tgui_color_t color);

/** Get a single pixel */
tgui_color_t tgui_get_pixel(const tgui_compositor_t *comp, int x, int y);

/** Draw a horizontal line */
void tgui_draw_hline(tgui_compositor_t *comp, int x, int y, int len, tgui_color_t color);

/** Draw a vertical line */
void tgui_draw_vline(tgui_compositor_t *comp, int x, int y, int len, tgui_color_t color);

/** Draw a rectangle outline */
void tgui_draw_rect(tgui_compositor_t *comp, int x, int y, int w, int h, tgui_color_t color);

/** Fill a rectangle */
void tgui_fill_rect(tgui_compositor_t *comp, int x, int y, int w, int h, tgui_color_t color);

/** Blend two colors using trit_or per channel (NDR blending) */
tgui_color_t tgui_blend(tgui_color_t a, tgui_color_t b);

/* ==== Window Management ================================================= */

/** Create a new window */
int tgui_window_create(tgui_compositor_t *comp, const char *title,
                       int x, int y, int w, int h, trit priority);

/** Destroy a window */
int tgui_window_destroy(tgui_compositor_t *comp, int win_id);

/** Move a window */
int tgui_window_move(tgui_compositor_t *comp, int win_id, int x, int y);

/** Set window visibility */
int tgui_window_set_visible(tgui_compositor_t *comp, int win_id, int visible);

/** Set a pixel in a window's local content buffer */
int tgui_window_set_pixel(tgui_compositor_t *comp, int win_id,
                          int x, int y, tgui_color_t color);

/** Composite all windows onto the framebuffer */
int tgui_composite(tgui_compositor_t *comp);

/* ==== Event Handling ==================================================== */

/** Push an event into the queue */
int tgui_event_push(tgui_compositor_t *comp, const tgui_event_t *evt);

/** Pop an event from the queue */
int tgui_event_pop(tgui_compositor_t *comp, tgui_event_t *evt);

/** Get pending event count */
int tgui_event_count(const tgui_compositor_t *comp);

/* ==== Statistics ========================================================= */

/** Get rendering statistics */
void tgui_stats(const tgui_compositor_t *comp,
                int *frames, int *pixels, int *events);

#ifdef __cplusplus
}
#endif

#endif /* TRIT_LINUX_TRIT_GUI_H */
