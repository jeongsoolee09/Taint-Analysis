// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.chilitags;

import org.bytedeco.javacpp.annotation.Index;
import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import static org.bytedeco.openblas.global.openblas_nolapack.*;
import static org.bytedeco.openblas.global.openblas.*;
import org.bytedeco.opencv.opencv_core.*;
import static org.bytedeco.opencv.global.opencv_core.*;
import org.bytedeco.opencv.opencv_imgproc.*;
import static org.bytedeco.opencv.global.opencv_imgproc.*;
import static org.bytedeco.opencv.global.opencv_imgcodecs.*;
import org.bytedeco.opencv.opencv_videoio.*;
import static org.bytedeco.opencv.global.opencv_videoio.*;
import org.bytedeco.opencv.opencv_highgui.*;
import static org.bytedeco.opencv.global.opencv_highgui.*;
import org.bytedeco.opencv.opencv_flann.*;
import static org.bytedeco.opencv.global.opencv_flann.*;
import org.bytedeco.opencv.opencv_features2d.*;
import static org.bytedeco.opencv.global.opencv_features2d.*;
import org.bytedeco.opencv.opencv_calib3d.*;
import static org.bytedeco.opencv.global.opencv_calib3d.*;
import org.bytedeco.opencv.opencv_video.*;
import static org.bytedeco.opencv.global.opencv_video.*;

import static org.bytedeco.chilitags.global.chilitags.*;


/**
    This class is the core of detection of chilitags.
    <p>
    Its main function is to find tags in an image, i.e. return the id and the
    position in the image of the corners of each detected chilitag.
    <p>
    It also provides some utilities, like encoding and decoding id's to/from
    bit matrices, or drawing a given tag.
 */
@Namespace("chilitags") @NoOffset @Properties(inherit = org.bytedeco.chilitags.presets.chilitags.class)
public class Chilitags extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public Chilitags(Pointer p) { super(p); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public Chilitags(long size) { super((Pointer)null); allocateArray(size); }
    private native void allocateArray(long size);
    @Override public Chilitags position(long position) {
        return (Chilitags)super.position(position);
    }
    @Override public Chilitags getPointer(long i) {
        return new Chilitags(this).position(position + i);
    }


/**
    Constructs a object ready to detect tags.
    It sets a default persistence of 5 frames for the tags, and a gain of 0.
    Please refer to the documentation of setFilter() for more detail.
    The default detection performance is balanced between accuracy and
    processing time (see Chilitags::FAST); it can be changed with
    setPerformance().
 */
public Chilitags() { super((Pointer)null); allocate(); }
private native void allocate();

/**
    Parameters to paliate with the imperfections of the detection.
    <p>
    @param persistence the number of frames in which a tag should be absent
    before being removed from the output of find(). 0 means that tags disappear
    directly if they are not detected.
    <p>
    @param gain a value between 0 and 1 corresponding to the weight of the
    previous (filtered) position in the new filtered position. 0 means that the
    latest position of the tag is returned.
 */
public native void setFilter(int persistence, float gain);

/**
    Values of the parameter to tell find() how to combine tracking and full
    detection.
    <p>
    find() relies on two different techniques to localize 2D tags in an image:
    \li The *detection* searches for edges in the full input image, keeps those
    wich looke like a quadrilateral, and check whether there is a valid
    bitmatrix inside it.
    \li The *tracking* compares two succesive input images and tries to update
    the position of tags that were previously detected. This process is
    significantly faster than the full detection, but can not detect new tags.
 */
/** enum chilitags::Chilitags::DetectionTrigger */
public static final int
/**
    First track results of the previous call to find(), then run a full
    detection on the same input image. The detected position overrides the
    position resulting from tracking if the same tag is both tracked and
    detected.
    <p>
    This improves the robustness of the detection, e.g. in the case where the
    tag has already been detected previously, but moves too fast to be detected
    again.
 */
    TRACK_AND_DETECT = 0,

/**
    Disable tracking: only full detections are performed. Compared to
    {@code TRACK_AND_DETECT}, {@code DETECT_ONLY} leads to a marginally faster processing,
    but may result in decreased detection performances when the tags move (due
    to motion blur).
     <p>
     {@code DETECT_ONLY} is however useful when Chilitags processes sequence of
     unrelated images, e.g.  in the batch processing of still images. In this
     case, tracking is useless and most likely generates false positives.
 */
    DETECT_ONLY = 1,

/**
    Perform tracking only. Tracking is drastically faster than full detection,
    but it can only report tags that have been already detected once: full
    detection must be run at least once to have some tags to track
    <p>
    Likewise, tracking can not detect new tags. A full detection needs to be
    run explicitely to detect (and then track) those. {@code TRACK_ONLY} is hence
    most useful when full control of when full detections occur is required
    (typically when precise control the time spend on processing one frame is
    needed). Use {@code DETECT_PERIODICALLY} to have automatic re-detection of tags
    every few frames.
    <p>
    Another interesting use case is to call {@code find()} with {@code TRACK_ONLY} as long
    as an expected (set of) tag(s) is found, and with {@code DETECT_ONLY} otherwise.
 */
    TRACK_ONLY = 2,

/**
    Periodically run a full detection.
    <p>
    {@code DETECT_PERIODICALLY} lets Chilitags use tracking most of the time, and
    eventually run a full detection.
    <p>
    {@code setDetectionPeriod()} allows to specify the number of frames between two
    full detection. It defaults to 15, i.e. out of 15 consecutive calls to
    {@code find()}, 1 will use a full detection, and the 14 others will only track
    previous results.
 */
    DETECT_PERIODICALLY = 3,

    /**
     * \brief Runs the detection in the background, with a period
     *
     * Runs the detection in a background thread, only tracking in the call to
     * {@code find()}.
     *
     * {@code setDetectionPeriod()} allows to specify the number of calls between two
     * detections. It defaults to 15, i.e. out of 15 consecutive calls to
     * {@code find()}, the background thread will be informed to run detection. After
     * this, a new detection will be done as soon as a new image frame is
     * presented in the call to {@code find()}. If the background thread takes more
     * time than 15 calls to {@code find()}, it will be running as frequently as
     * possible, i.e the same as {@code BACKGROUND_DETECT_ALWAYS}.
     *
     * This cannot be used without enabling multithreading support during
     * build.
     */
    ASYNC_DETECT_PERIODICALLY = 4,

    /**
     * \brief Runs the detection in the background, as frequently as possible
     *
     * Runs the detection in a background thread, only tracking in the call to
     * {@code find()}. The detection is run as frequently as possible, i.e a new
     * detection is started as soon as the new image frame is presented in the
     * call to {@code find()} after the previous detection is finished.
     *
     * This cannot be used without enabling multithreading support during
     * build.
     */
    ASYNC_DETECT_ALWAYS = 5;

/**
    This is the main method of Chilitags.
    <p>
    @return the detected tags, in the form of a mapping between their id's and
    the position of their four corners.
    <p>
    @param inputImage an OpenCV image (gray or BGR)
    <p>
    @param detectionTrigger specifies how to combine tracking and full
    detection. Tracking is drastically faster, but it can at best return tags
    previously found; it won't find new ones, but can lose some. See
    Chilitags::DetectionTrigger for a description of the possible values.
 */
public native @ByVal TagCornerMap find(
    @Const @ByRef Mat inputImage,
    @Cast("chilitags::Chilitags::DetectionTrigger") int detectionTrigger/*=chilitags::Chilitags::DETECT_ONLY*/);
public native @ByVal TagCornerMap find(
    @Const @ByRef Mat inputImage);

/**
    When the detection trigger is Chilitags::DETECT_PERIODICALLY, {@code period}
    specifies the number of frames between each full detection. The
    default is 15, which means that out of 15 consecutive calls to find(),
    one will use a full detection, and the 14 others will only track
    previous results.
 */
public native void setDetectionPeriod(int period);

/**
    Preset groups of parameters (for setPerformance()) to adjust  the
    compromise between processing time and accuracy of detection.
 */
/** enum chilitags::Chilitags::PerformancePreset */
public static final int
/**
    Favor speed over accuracy: no corner refinment, no subsampling.
 */
    FASTER = 0,
/**
    Balance speed and accuracy (default): corners are refined, no subsampling.
 */
    FAST = 1,
/**
    Favor robustness over accuracy: corner are refined, input is
    subsampled down to 160 pixels wide.
 */
    ROBUST = 2;

/**
    Applies one of the performance tuning preset (See PerformancePreset). To
    tune more finely the performance trade-offs, see setCornerRefinment(),
    setMaxInputWidth(), and setMinInputWidth().
 */
public native void setPerformance(@Cast("chilitags::Chilitags::PerformancePreset") int preset);

//@{

/**
    Enable or disable the corner refinement. It is enabled (true) by default.
    When disabled, the processing time is reduced by ~33%, but the coordinates
    of the tags lose their sub-pixel precision, and there is a marginally
    higher level of false negatives.
 */
public native void setCornerRefinement(@Cast("bool") boolean refineCorners);

/**
    Ensures that the image used as input for the detection is at most
    {@code maxWidth} wide. The smaller, the faster, but tags smaller than 20 pixels
    won't be detected.
    <p>
    @param maxWidth the width to which input images should be reduced to, or 0
    if no resizing should occur (default).
 */
public native void setMaxInputWidth(int maxWidth);

/**
    Chilitags searches for tags on the input image and on subsamples reduced to
    50%, 25%, 12.5%, etc. of the original size. The subsamples are reduced as
    long as they are at least {@code minWidth} wide. This value can be changed to
    adjust the lower limit of subsampling. For example, the Chilitags::ROBUST
    performance preset calls {@code setMinInputWidth(160)}.
    <p>
    If {@code minWidth} is set to 0, subsampling is completely disabled, i.e. tags
    are searched only on the original input image. This is the behaviour set by
    Chilitags::FAST, i.e. the default behaviour.
    <p>
    Disabling the subsampling reduces the processing time by ~40%, but large
    tags (having sides larger than hundreds of pixels) are likely to be missed.
 */
public native void setMinInputWidth(int minWidth);

//@}

//@{
/**
    Finds the black and white, 6x6 matrix corresponding to the given id.
    <p>
    @param id the id of the tag to encode, between  0 (included) and 1024
    (excluded).
    <p>
    @return the 36-element bit matrix coding the given id (black is 0,
    white is 1)
 */

/**
    Finds the tag id corresponding given the black and white, 6x6 matrix.
    <p>
    @return the id decoded from the bit matrix, between  0 (included) and 1024
    (excluded). If the bit matrix did not code a valid id, -1 is returned.
    <p>
    @param bits the 36-element bit matrix coding the given id (black is 0,
    white is 1)
 */

/**
    @return an OpenCV image of a given tag.
    <p>
    @param id the id of the tag to draw, between [0,1024)
    <p>
    @param cellSize the (integer) scale factor with which to draw the tag. In
    other words, every bit of the data matrix of the tag will be {@code cellSize}
    large.
    <p>
    @param withMargin a boolean coding whether the returned image of the tag
    should be surrounded by a white frame, ensuring that the edges of the tag
    will contrast with the background.
    <p>
    @param color the RGB color with which to draw the tag. Values are integers
    within [0,255]. The darker, the better. Black is default and optimal.
 */
public native @ByVal Mat draw(
    int id,
    int cellSize/*=1*/,
    @Cast("bool") boolean withMargin/*=false*/,
    @ByVal(nullValue = "cv::Scalar(0,0,0)") Scalar color);
public native @ByVal Mat draw(
    int id);

//@}

}
