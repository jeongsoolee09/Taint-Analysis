// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.tesseract;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import org.bytedeco.leptonica.*;
import static org.bytedeco.leptonica.global.lept.*;

import static org.bytedeco.tesseract.global.tesseract.*;


/**
 * Class to iterate over tesseract page structure, providing access to all
 * levels of the page hierarchy, without including any tesseract headers or
 * having to handle any tesseract structures.
 * WARNING! This class points to data held within the TessBaseAPI class, and
 * therefore can only be used while the TessBaseAPI class still exists and
 * has not been subjected to a call of Init, SetImage, Recognize, Clear, End
 * DetectOS, or anything else that changes the internal PAGE_RES.
 * See apitypes.h for the definition of PageIteratorLevel.
 * See also ResultIterator, derived from PageIterator, which adds in the
 * ability to access OCR output with text-specific methods.
 */

@Namespace("tesseract") @NoOffset @Properties(inherit = org.bytedeco.tesseract.presets.tesseract.class)
public class PageIterator extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public PageIterator(Pointer p) { super(p); }

  /**
   * page_res and tesseract come directly from the BaseAPI.
   * The rectangle parameters are copied indirectly from the Thresholder,
   * via the BaseAPI. They represent the coordinates of some rectangle in an
   * original image (in top-left-origin coordinates) and therefore the top-left
   * needs to be added to any output boxes in order to specify coordinates
   * in the original image. See TessBaseAPI::SetRectangle.
   * The scale and scaled_yres are in case the Thresholder scaled the image
   * rectangle prior to thresholding. Any coordinates in tesseract's image
   * must be divided by scale before adding (rect_left, rect_top).
   * The scaled_yres indicates the effective resolution of the binary image
   * that tesseract has been given by the Thresholder.
   * After the constructor, Begin has already been called.
   */
  public PageIterator(PAGE_RES page_res, Tesseract tesseract,
                 int scale, int scaled_yres,
                 int rect_left, int rect_top,
                 int rect_width, int rect_height) { super((Pointer)null); allocate(page_res, tesseract, scale, scaled_yres, rect_left, rect_top, rect_width, rect_height); }
  private native void allocate(PAGE_RES page_res, Tesseract tesseract,
                 int scale, int scaled_yres,
                 int rect_left, int rect_top,
                 int rect_width, int rect_height);

  /**
   * Page/ResultIterators may be copied! This makes it possible to iterate over
   * all the objects at a lower level, while maintaining an iterator to
   * objects at a higher level. These constructors DO NOT CALL Begin, so
   * iterations will continue from the location of src.
   */
  public PageIterator(@Const @ByRef PageIterator src) { super((Pointer)null); allocate(src); }
  private native void allocate(@Const @ByRef PageIterator src);
  public native @Const @ByRef @Name("operator =") PageIterator put(@Const @ByRef PageIterator src);

  /** Are we positioned at the same location as other? */
  public native @Cast("bool") boolean PositionedAtSameWord(@Const PAGE_RES_IT other);

  // ============= Moving around within the page ============.

  /**
   * Moves the iterator to point to the start of the page to begin an
   * iteration.
   */
  public native void Begin();

  /**
   * Moves the iterator to the beginning of the paragraph.
   * This class implements this functionality by moving it to the zero indexed
   * blob of the first (leftmost) word on the first row of the paragraph.
   */
  public native void RestartParagraph();

  /**
   * Return whether this iterator points anywhere in the first textline of a
   * paragraph.
   */
  public native @Cast("bool") boolean IsWithinFirstTextlineOfParagraph();

  /**
   * Moves the iterator to the beginning of the text line.
   * This class implements this functionality by moving it to the zero indexed
   * blob of the first (leftmost) word of the row.
   */
  public native void RestartRow();

  /**
   * Moves to the start of the next object at the given level in the
   * page hierarchy, and returns false if the end of the page was reached.
   * NOTE that RIL_SYMBOL will skip non-text blocks, but all other
   * PageIteratorLevel level values will visit each non-text block once.
   * Think of non text blocks as containing a single para, with a single line,
   * with a single imaginary word.
   * Calls to Next with different levels may be freely intermixed.
   * This function iterates words in right-to-left scripts correctly, if
   * the appropriate language has been loaded into Tesseract.
   */
  public native @Cast("bool") boolean Next(@Cast("tesseract::PageIteratorLevel") int level);

  /**
   * Returns true if the iterator is at the start of an object at the given
   * level.
   *
   * For instance, suppose an iterator it is pointed to the first symbol of the
   * first word of the third line of the second paragraph of the first block in
   * a page, then:
   *   it.IsAtBeginningOf(RIL_BLOCK) = false
   *   it.IsAtBeginningOf(RIL_PARA) = false
   *   it.IsAtBeginningOf(RIL_TEXTLINE) = true
   *   it.IsAtBeginningOf(RIL_WORD) = true
   *   it.IsAtBeginningOf(RIL_SYMBOL) = true
   */
  public native @Cast("bool") boolean IsAtBeginningOf(@Cast("tesseract::PageIteratorLevel") int level);

  /**
   * Returns whether the iterator is positioned at the last element in a
   * given level. (e.g. the last word in a line, the last line in a block)
   *
   *     Here's some two-paragraph example
   *   text.  It starts off innocuously
   *   enough but quickly turns bizarre.
   *     The author inserts a cornucopia
   *   of words to guard against confused
   *   references.
   *
   * Now take an iterator it pointed to the start of "bizarre."
   *  it.IsAtFinalElement(RIL_PARA, RIL_SYMBOL) = false
   *  it.IsAtFinalElement(RIL_PARA, RIL_WORD) = true
   *  it.IsAtFinalElement(RIL_BLOCK, RIL_WORD) = false
   */
  public native @Cast("bool") boolean IsAtFinalElement(@Cast("tesseract::PageIteratorLevel") int level,
                                  @Cast("tesseract::PageIteratorLevel") int element);

  /**
   * Returns whether this iterator is positioned
   *   before other:   -1
   *   equal to other:  0
   *   after other:     1
   */
  public native int Cmp(@Const @ByRef PageIterator other);

  // ============= Accessing data ==============.
  // Coordinate system:
  // Integer coordinates are at the cracks between the pixels.
  // The top-left corner of the top-left pixel in the image is at (0,0).
  // The bottom-right corner of the bottom-right pixel in the image is at
  // (width, height).
  // Every bounding box goes from the top-left of the top-left contained
  // pixel to the bottom-right of the bottom-right contained pixel, so
  // the bounding box of the single top-left pixel in the image is:
  // (0,0)->(1,1).
  // If an image rectangle has been set in the API, then returned coordinates
  // relate to the original (full) image, rather than the rectangle.

  /**
   * Controls what to include in a bounding box. Bounding boxes of all levels
   * between RIL_WORD and RIL_BLOCK can include or exclude potential diacritics.
   * Between layout analysis and recognition, it isn't known where all
   * diacritics belong, so this control is used to include or exclude some
   * diacritics that are above or below the main body of the word. In most cases
   * where the placement is obvious, and after recognition, it doesn't make as
   * much difference, as the diacritics will already be included in the word.
   */
  public native void SetBoundingBoxComponents(@Cast("bool") boolean include_upper_dots,
                                  @Cast("bool") boolean include_lower_dots);

  /**
   * Returns the bounding rectangle of the current object at the given level.
   * See comment on coordinate system above.
   * Returns false if there is no such object at the current position.
   * The returned bounding box is guaranteed to match the size and position
   * of the image returned by GetBinaryImage, but may clip foreground pixels
   * from a grey image. The padding argument to GetImage can be used to expand
   * the image to include more foreground pixels. See GetImage below.
   */
  public native @Cast("bool") boolean BoundingBox(@Cast("tesseract::PageIteratorLevel") int level,
                     IntPointer left, IntPointer top, IntPointer right, IntPointer bottom);
  public native @Cast("bool") boolean BoundingBox(@Cast("tesseract::PageIteratorLevel") int level,
                     IntBuffer left, IntBuffer top, IntBuffer right, IntBuffer bottom);
  public native @Cast("bool") boolean BoundingBox(@Cast("tesseract::PageIteratorLevel") int level,
                     int[] left, int[] top, int[] right, int[] bottom);
  public native @Cast("bool") boolean BoundingBox(@Cast("tesseract::PageIteratorLevel") int level, int padding,
                     IntPointer left, IntPointer top, IntPointer right, IntPointer bottom);
  public native @Cast("bool") boolean BoundingBox(@Cast("tesseract::PageIteratorLevel") int level, int padding,
                     IntBuffer left, IntBuffer top, IntBuffer right, IntBuffer bottom);
  public native @Cast("bool") boolean BoundingBox(@Cast("tesseract::PageIteratorLevel") int level, int padding,
                     int[] left, int[] top, int[] right, int[] bottom);
  /**
   * Returns the bounding rectangle of the object in a coordinate system of the
   * working image rectangle having its origin at (rect_left_, rect_top_) with
   * respect to the original image and is scaled by a factor scale_.
   */
  public native @Cast("bool") boolean BoundingBoxInternal(@Cast("tesseract::PageIteratorLevel") int level,
                             IntPointer left, IntPointer top, IntPointer right, IntPointer bottom);
  public native @Cast("bool") boolean BoundingBoxInternal(@Cast("tesseract::PageIteratorLevel") int level,
                             IntBuffer left, IntBuffer top, IntBuffer right, IntBuffer bottom);
  public native @Cast("bool") boolean BoundingBoxInternal(@Cast("tesseract::PageIteratorLevel") int level,
                             int[] left, int[] top, int[] right, int[] bottom);

  /** Returns whether there is no object of a given level. */
  public native @Cast("bool") boolean Empty(@Cast("tesseract::PageIteratorLevel") int level);

  /**
   * Returns the type of the current block. See apitypes.h for
   * PolyBlockType.
   */
  public native @Cast("PolyBlockType") int BlockType();

  /**
   * Returns the polygon outline of the current block. The returned Pta must
   * be ptaDestroy-ed after use. Note that the returned Pta lists the vertices
   * of the polygon, and the last edge is the line segment between the last
   * point and the first point. nullptr will be returned if the iterator is
   * at the end of the document or layout analysis was not used.
   */
  public native PTA BlockPolygon();

  /**
   * Returns a binary image of the current object at the given level.
   * The position and size match the return from BoundingBoxInternal, and so
   * this could be upscaled with respect to the original input image.
   * Use pixDestroy to delete the image after use.
   */
  public native PIX GetBinaryImage(@Cast("tesseract::PageIteratorLevel") int level);

  /**
   * Returns an image of the current object at the given level in greyscale
   * if available in the input. To guarantee a binary image use BinaryImage.
   * NOTE that in order to give the best possible image, the bounds are
   * expanded slightly over the binary connected component, by the supplied
   * padding, so the top-left position of the returned image is returned
   * in (left,top). These will most likely not match the coordinates
   * returned by BoundingBox.
   * If you do not supply an original image, you will get a binary one.
   * Use pixDestroy to delete the image after use.
   */
  public native PIX GetImage(@Cast("tesseract::PageIteratorLevel") int level, int padding, PIX original_img,
                  IntPointer left, IntPointer top);
  public native PIX GetImage(@Cast("tesseract::PageIteratorLevel") int level, int padding, PIX original_img,
                  IntBuffer left, IntBuffer top);
  public native PIX GetImage(@Cast("tesseract::PageIteratorLevel") int level, int padding, PIX original_img,
                  int[] left, int[] top);

  /**
   * Returns the baseline of the current object at the given level.
   * The baseline is the line that passes through (x1, y1) and (x2, y2).
   * WARNING: with vertical text, baselines may be vertical!
   * Returns false if there is no baseline at the current position.
   */
  public native @Cast("bool") boolean Baseline(@Cast("tesseract::PageIteratorLevel") int level,
                  IntPointer x1, IntPointer y1, IntPointer x2, IntPointer y2);
  public native @Cast("bool") boolean Baseline(@Cast("tesseract::PageIteratorLevel") int level,
                  IntBuffer x1, IntBuffer y1, IntBuffer x2, IntBuffer y2);
  public native @Cast("bool") boolean Baseline(@Cast("tesseract::PageIteratorLevel") int level,
                  int[] x1, int[] y1, int[] x2, int[] y2);

  /**
   * Returns orientation for the block the iterator points to.
   *   orientation, writing_direction, textline_order: see publictypes.h
   *   deskew_angle: after rotating the block so the text orientation is
   *                 upright, how many radians does one have to rotate the
   *                 block anti-clockwise for it to be level?
   *                   -Pi/4 <= deskew_angle <= Pi/4
   */
  public native void Orientation(@Cast("tesseract::Orientation*") IntPointer orientation,
                     @Cast("tesseract::WritingDirection*") IntPointer writing_direction,
                     @Cast("tesseract::TextlineOrder*") IntPointer textline_order,
                     FloatPointer deskew_angle);
  public native void Orientation(@Cast("tesseract::Orientation*") IntBuffer orientation,
                     @Cast("tesseract::WritingDirection*") IntBuffer writing_direction,
                     @Cast("tesseract::TextlineOrder*") IntBuffer textline_order,
                     FloatBuffer deskew_angle);
  public native void Orientation(@Cast("tesseract::Orientation*") int[] orientation,
                     @Cast("tesseract::WritingDirection*") int[] writing_direction,
                     @Cast("tesseract::TextlineOrder*") int[] textline_order,
                     float[] deskew_angle);

  /**
   * Returns information about the current paragraph, if available.
   *
   *   justification -
   *     LEFT if ragged right, or fully justified and script is left-to-right.
   *     RIGHT if ragged left, or fully justified and script is right-to-left.
   *     unknown if it looks like source code or we have very few lines.
   *   is_list_item -
   *     true if we believe this is a member of an ordered or unordered list.
   *   is_crown -
   *     true if the first line of the paragraph is aligned with the other
   *     lines of the paragraph even though subsequent paragraphs have first
   *     line indents.  This typically indicates that this is the continuation
   *     of a previous paragraph or that it is the very first paragraph in
   *     the chapter.
   *   first_line_indent -
   *     For LEFT aligned paragraphs, the first text line of paragraphs of
   *     this kind are indented this many pixels from the left edge of the
   *     rest of the paragraph.
   *     for RIGHT aligned paragraphs, the first text line of paragraphs of
   *     this kind are indented this many pixels from the right edge of the
   *     rest of the paragraph.
   *     NOTE 1: This value may be negative.
   *     NOTE 2: if *is_crown == true, the first line of this paragraph is
   *             actually flush, and first_line_indent is set to the "common"
   *             first_line_indent for subsequent paragraphs in this block
   *             of text.
   */
  public native void ParagraphInfo(@Cast("tesseract::ParagraphJustification*") IntPointer justification,
                       @Cast("bool*") BoolPointer is_list_item,
                       @Cast("bool*") BoolPointer is_crown,
                       IntPointer first_line_indent);
  public native void ParagraphInfo(@Cast("tesseract::ParagraphJustification*") IntBuffer justification,
                       @Cast("bool*") boolean[] is_list_item,
                       @Cast("bool*") boolean[] is_crown,
                       IntBuffer first_line_indent);
  public native void ParagraphInfo(@Cast("tesseract::ParagraphJustification*") int[] justification,
                       @Cast("bool*") BoolPointer is_list_item,
                       @Cast("bool*") BoolPointer is_crown,
                       int[] first_line_indent);
  public native void ParagraphInfo(@Cast("tesseract::ParagraphJustification*") IntPointer justification,
                       @Cast("bool*") boolean[] is_list_item,
                       @Cast("bool*") boolean[] is_crown,
                       IntPointer first_line_indent);
  public native void ParagraphInfo(@Cast("tesseract::ParagraphJustification*") IntBuffer justification,
                       @Cast("bool*") BoolPointer is_list_item,
                       @Cast("bool*") BoolPointer is_crown,
                       IntBuffer first_line_indent);
  public native void ParagraphInfo(@Cast("tesseract::ParagraphJustification*") int[] justification,
                       @Cast("bool*") boolean[] is_list_item,
                       @Cast("bool*") boolean[] is_crown,
                       int[] first_line_indent);

  // If the current WERD_RES (it_->word()) is not nullptr, sets the BlamerBundle
  // of the current word to the given pointer (takes ownership of the pointer)
  // and returns true.
  // Can only be used when iterating on the word level.
  public native @Cast("bool") boolean SetWordBlamerBundle(BlamerBundle blamer_bundle);
}
