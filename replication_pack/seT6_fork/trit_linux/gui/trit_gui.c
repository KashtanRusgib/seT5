/**
 * @file trit_gui.c
 * @brief Trit Linux — Ternary GUI Framework Implementation
 *
 * Implements a minimal compositor with ternary color model, framebuffer
 * drawing primitives, trit-priority window stacking, and event handling.
 * All operations run in user-space, isolated from the kernel.
 *
 * Enhancement 3: "Graphical User Interface (GUI) and Display Drivers"
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include "trit_gui.h"

/* ==================================================================== */
/*  Initialization                                                      */
/* ==================================================================== */

int tgui_init(tgui_compositor_t *comp) {
    if (!comp) return -1;

    memset(comp, 0, sizeof(*comp));

    /* Clear framebuffer to black */
    tgui_color_t black = TGUI_COLOR_BLACK;
    for (int i = 0; i < TGUI_FB_PIXELS; i++) {
        comp->framebuffer[i] = black;
    }

    /* Initialize all window slots as inactive */
    for (int i = 0; i < TGUI_MAX_WINDOWS; i++) {
        comp->windows[i].id = -1;
        comp->windows[i].visible = 0;
    }

    comp->window_count = 0;
    comp->evt_head = comp->evt_tail = comp->evt_count = 0;
    comp->frames_rendered = 0;
    comp->pixels_drawn = 0;
    comp->events_processed = 0;
    comp->initialized = 1;

    return 0;
}

/* ==================================================================== */
/*  Framebuffer Operations                                              */
/* ==================================================================== */

void tgui_clear(tgui_compositor_t *comp, tgui_color_t color) {
    if (!comp || !comp->initialized) return;

    for (int i = 0; i < TGUI_FB_PIXELS; i++) {
        comp->framebuffer[i] = color;
    }
    comp->pixels_drawn += TGUI_FB_PIXELS;
}

int tgui_set_pixel(tgui_compositor_t *comp, int x, int y, tgui_color_t color) {
    if (!comp || !comp->initialized) return -1;

    /* Bounds check against framebuffer dimensions */
    if (x < 0 || x >= TGUI_FB_WIDTH || y < 0 || y >= TGUI_FB_HEIGHT) {
        return -1; /* Out of bounds */
    }

    comp->framebuffer[y * TGUI_FB_WIDTH + x] = color;
    comp->pixels_drawn++;
    return 0;
}

tgui_color_t tgui_get_pixel(const tgui_compositor_t *comp, int x, int y) {
    tgui_color_t black = TGUI_COLOR_BLACK;
    if (!comp || !comp->initialized) return black;
    if (x < 0 || x >= TGUI_FB_WIDTH || y < 0 || y >= TGUI_FB_HEIGHT) {
        return black;
    }
    return comp->framebuffer[y * TGUI_FB_WIDTH + x];
}

void tgui_draw_hline(tgui_compositor_t *comp, int x, int y, int len,
                     tgui_color_t color) {
    if (!comp || !comp->initialized) return;

    /* Draw a horizontal line from (x,y) to (x+len-1, y) */
    for (int i = 0; i < len; i++) {
        tgui_set_pixel(comp, x + i, y, color);
    }
}

void tgui_draw_vline(tgui_compositor_t *comp, int x, int y, int len,
                     tgui_color_t color) {
    if (!comp || !comp->initialized) return;

    /* Draw a vertical line from (x,y) to (x, y+len-1) */
    for (int i = 0; i < len; i++) {
        tgui_set_pixel(comp, x, y + i, color);
    }
}

void tgui_draw_rect(tgui_compositor_t *comp, int x, int y, int w, int h,
                    tgui_color_t color) {
    if (!comp || !comp->initialized) return;

    /* Draw four sides of a rectangle outline */
    tgui_draw_hline(comp, x, y, w, color);         /* Top edge    */
    tgui_draw_hline(comp, x, y + h - 1, w, color); /* Bottom edge */
    tgui_draw_vline(comp, x, y, h, color);          /* Left edge   */
    tgui_draw_vline(comp, x + w - 1, y, h, color);  /* Right edge  */
}

void tgui_fill_rect(tgui_compositor_t *comp, int x, int y, int w, int h,
                    tgui_color_t color) {
    if (!comp || !comp->initialized) return;

    /* Fill a solid rectangle */
    for (int row = y; row < y + h; row++) {
        for (int col = x; col < x + w; col++) {
            tgui_set_pixel(comp, col, row, color);
        }
    }
}

tgui_color_t tgui_blend(tgui_color_t a, tgui_color_t b) {
    /*
     * NDR (Non-Destructive Read) blending:
     * Apply trit_or per channel — the brighter value dominates.
     * This is the ternary equivalent of additive blending.
     */
    tgui_color_t result;
    result.r = trit_or(a.r, b.r);
    result.g = trit_or(a.g, b.g);
    result.b = trit_or(a.b, b.b);
    return result;
}

/* ==================================================================== */
/*  Window Management                                                   */
/* ==================================================================== */

int tgui_window_create(tgui_compositor_t *comp, const char *title,
                       int x, int y, int w, int h, trit priority) {
    if (!comp || !comp->initialized) return -1;
    if (comp->window_count >= TGUI_MAX_WINDOWS) return -1;

    /* Clamp window dimensions to framebuffer */
    if (w <= 0 || h <= 0) return -1;
    if (w > TGUI_FB_WIDTH)  w = TGUI_FB_WIDTH;
    if (h > TGUI_FB_HEIGHT) h = TGUI_FB_HEIGHT;

    /* Find a free window slot */
    for (int i = 0; i < TGUI_MAX_WINDOWS; i++) {
        if (comp->windows[i].id == -1) {
            tgui_window_t *win = &comp->windows[i];
            win->id = i;
            if (title) {
                strncpy(win->title, title, TGUI_TITLE_LEN - 1);
                win->title[TGUI_TITLE_LEN - 1] = '\0';
            }
            win->x = x;
            win->y = y;
            win->width = w;
            win->height = h;
            win->priority = priority;
            win->bg_color = TGUI_COLOR_GRAY; /* Default background */
            win->visible = 1;
            win->dirty = 1;
            win->content_width = w;
            win->content_height = h;

            /* Clear window content to background color */
            for (int j = 0; j < w * h && j < TGUI_FB_PIXELS; j++) {
                win->content[j] = win->bg_color;
            }

            comp->window_count++;
            return i; /* Return window ID */
        }
    }

    return -1; /* No free slots */
}

int tgui_window_destroy(tgui_compositor_t *comp, int win_id) {
    if (!comp || win_id < 0 || win_id >= TGUI_MAX_WINDOWS) return -1;
    if (comp->windows[win_id].id == -1) return -1;

    comp->windows[win_id].id = -1;
    comp->windows[win_id].visible = 0;
    comp->window_count--;

    return 0;
}

int tgui_window_move(tgui_compositor_t *comp, int win_id, int x, int y) {
    if (!comp || win_id < 0 || win_id >= TGUI_MAX_WINDOWS) return -1;
    if (comp->windows[win_id].id == -1) return -1;

    comp->windows[win_id].x = x;
    comp->windows[win_id].y = y;
    comp->windows[win_id].dirty = 1;

    return 0;
}

int tgui_window_set_visible(tgui_compositor_t *comp, int win_id, int visible) {
    if (!comp || win_id < 0 || win_id >= TGUI_MAX_WINDOWS) return -1;
    if (comp->windows[win_id].id == -1) return -1;

    comp->windows[win_id].visible = visible ? 1 : 0;
    comp->windows[win_id].dirty = 1;

    return 0;
}

int tgui_window_set_pixel(tgui_compositor_t *comp, int win_id,
                          int x, int y, tgui_color_t color) {
    if (!comp || win_id < 0 || win_id >= TGUI_MAX_WINDOWS) return -1;

    tgui_window_t *win = &comp->windows[win_id];
    if (win->id == -1) return -1;

    /* Bounds check against window content dimensions */
    if (x < 0 || x >= win->content_width ||
        y < 0 || y >= win->content_height) {
        return -1;
    }

    win->content[y * win->content_width + x] = color;
    win->dirty = 1;

    return 0;
}

int tgui_composite(tgui_compositor_t *comp) {
    if (!comp || !comp->initialized) return -1;

    /*
     * Composite all visible windows onto the framebuffer.
     * Paint order: -1 (background) first, then 0, then +1 (foreground).
     * This ensures high-priority windows appear on top.
     */
    tgui_color_t black = TGUI_COLOR_BLACK;
    for (int i = 0; i < TGUI_FB_PIXELS; i++) {
        comp->framebuffer[i] = black;
    }

    /* Three-pass render: background → normal → foreground */
    trit priorities[3] = { TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };
    for (int pass = 0; pass < 3; pass++) {
        for (int w = 0; w < TGUI_MAX_WINDOWS; w++) {
            tgui_window_t *win = &comp->windows[w];
            if (win->id == -1 || !win->visible) continue;
            if (win->priority != priorities[pass]) continue;

            /* Blit window content to framebuffer at (win->x, win->y) */
            for (int wy = 0; wy < win->content_height; wy++) {
                for (int wx = 0; wx < win->content_width; wx++) {
                    int fb_x = win->x + wx;
                    int fb_y = win->y + wy;
                    if (fb_x >= 0 && fb_x < TGUI_FB_WIDTH &&
                        fb_y >= 0 && fb_y < TGUI_FB_HEIGHT) {
                        int fb_idx = fb_y * TGUI_FB_WIDTH + fb_x;
                        int win_idx = wy * win->content_width + wx;

                        /* Use NDR blending for compositing */
                        comp->framebuffer[fb_idx] =
                            tgui_blend(comp->framebuffer[fb_idx],
                                       win->content[win_idx]);
                    }
                }
            }

            win->dirty = 0;
        }
    }

    comp->frames_rendered++;
    return 0;
}

/* ==================================================================== */
/*  Event Handling                                                      */
/* ==================================================================== */

int tgui_event_push(tgui_compositor_t *comp, const tgui_event_t *evt) {
    if (!comp || !evt || !comp->initialized) return -1;
    if (comp->evt_count >= TGUI_MAX_EVENTS) return -1;

    comp->events[comp->evt_tail] = *evt;
    comp->evt_tail = (comp->evt_tail + 1) % TGUI_MAX_EVENTS;
    comp->evt_count++;

    return 0;
}

int tgui_event_pop(tgui_compositor_t *comp, tgui_event_t *evt) {
    if (!comp || !evt || !comp->initialized) return -1;
    if (comp->evt_count == 0) return -1;

    *evt = comp->events[comp->evt_head];
    comp->evt_head = (comp->evt_head + 1) % TGUI_MAX_EVENTS;
    comp->evt_count--;
    comp->events_processed++;

    return 0;
}

int tgui_event_count(const tgui_compositor_t *comp) {
    if (!comp) return 0;
    return comp->evt_count;
}

/* ==================================================================== */
/*  Statistics                                                          */
/* ==================================================================== */

void tgui_stats(const tgui_compositor_t *comp,
                int *frames, int *pixels, int *events) {
    if (!comp) return;
    if (frames) *frames = comp->frames_rendered;
    if (pixels) *pixels = comp->pixels_drawn;
    if (events) *events = comp->events_processed;
}
