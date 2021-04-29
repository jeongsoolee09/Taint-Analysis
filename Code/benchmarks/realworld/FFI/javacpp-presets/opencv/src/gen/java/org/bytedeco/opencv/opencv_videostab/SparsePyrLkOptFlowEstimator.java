// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.opencv.opencv_videostab;

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
import org.bytedeco.opencv.opencv_objdetect.*;
import static org.bytedeco.opencv.global.opencv_objdetect.*;
import org.bytedeco.opencv.opencv_dnn.*;
import static org.bytedeco.opencv.global.opencv_dnn.*;
import org.bytedeco.opencv.opencv_video.*;
import static org.bytedeco.opencv.global.opencv_video.*;
import org.bytedeco.opencv.opencv_ximgproc.*;
import static org.bytedeco.opencv.global.opencv_ximgproc.*;
import org.bytedeco.opencv.opencv_optflow.*;
import static org.bytedeco.opencv.global.opencv_optflow.*;
import org.bytedeco.opencv.opencv_photo.*;
import static org.bytedeco.opencv.global.opencv_photo.*;

import static org.bytedeco.opencv.global.opencv_videostab.*;


@Namespace("cv::videostab") @Properties(inherit = org.bytedeco.opencv.presets.opencv_videostab.class)
public class SparsePyrLkOptFlowEstimator extends PyrLkOptFlowEstimatorBase {
    static { Loader.load(); }
    /** Default native constructor. */
    public SparsePyrLkOptFlowEstimator() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public SparsePyrLkOptFlowEstimator(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public SparsePyrLkOptFlowEstimator(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public SparsePyrLkOptFlowEstimator position(long position) {
        return (SparsePyrLkOptFlowEstimator)super.position(position);
    }
    @Override public SparsePyrLkOptFlowEstimator getPointer(long i) {
        return new SparsePyrLkOptFlowEstimator(this).position(position + i);
    }
    public ISparseOptFlowEstimator asISparseOptFlowEstimator() { return asISparseOptFlowEstimator(this); }
    @Namespace public static native @Name("static_cast<cv::videostab::ISparseOptFlowEstimator*>") ISparseOptFlowEstimator asISparseOptFlowEstimator(SparsePyrLkOptFlowEstimator pointer);

    public native void run(
                @ByVal Mat frame0, @ByVal Mat frame1, @ByVal Mat points0, @ByVal Mat points1,
                @ByVal Mat status, @ByVal Mat errors);
    public native void run(
                @ByVal UMat frame0, @ByVal UMat frame1, @ByVal UMat points0, @ByVal UMat points1,
                @ByVal UMat status, @ByVal UMat errors);
    public native void run(
                @ByVal GpuMat frame0, @ByVal GpuMat frame1, @ByVal GpuMat points0, @ByVal GpuMat points1,
                @ByVal GpuMat status, @ByVal GpuMat errors);
}