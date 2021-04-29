// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.opencv.opencv_objdetect;

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

import static org.bytedeco.opencv.global.opencv_objdetect.*;


/** \addtogroup objdetect
 *  \{ */

@Namespace("cv") @NoOffset @Properties(inherit = org.bytedeco.opencv.presets.opencv_objdetect.class)
public class DetectionBasedTracker extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public DetectionBasedTracker(Pointer p) { super(p); }

        @NoOffset public static class Parameters extends Pointer {
            static { Loader.load(); }
            /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
            public Parameters(Pointer p) { super(p); }
            /** Native array allocator. Access with {@link Pointer#position(long)}. */
            public Parameters(long size) { super((Pointer)null); allocateArray(size); }
            private native void allocateArray(long size);
            @Override public Parameters position(long position) {
                return (Parameters)super.position(position);
            }
            @Override public Parameters getPointer(long i) {
                return new Parameters(this).position(position + i);
            }
        
            public native int maxTrackLifetime(); public native Parameters maxTrackLifetime(int setter);
            public native int minDetectionPeriod(); public native Parameters minDetectionPeriod(int setter); //the minimal time between run of the big object detector (on the whole frame) in ms (1000 mean 1 sec), default=0

            public Parameters() { super((Pointer)null); allocate(); }
            private native void allocate();
        }

        @NoOffset public static class IDetector extends Pointer {
            static { Loader.load(); }
            /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
            public IDetector(Pointer p) { super(p); }
        

                public native void detect(@Const @ByRef Mat image, @ByRef RectVector objects);

                public native void setMinObjectSize(@Const @ByRef Size min);
                public native void setMaxObjectSize(@Const @ByRef Size max);
                public native @ByVal Size getMinObjectSize();
                public native @ByVal Size getMaxObjectSize();
                public native float getScaleFactor();
                public native void setScaleFactor(float value);
                public native int getMinNeighbours();
                public native void setMinNeighbours(int value);
        }

        public DetectionBasedTracker(@Ptr IDetector mainDetector, @Ptr IDetector trackingDetector, @Const @ByRef Parameters params) { super((Pointer)null); allocate(mainDetector, trackingDetector, params); }
        private native void allocate(@Ptr IDetector mainDetector, @Ptr IDetector trackingDetector, @Const @ByRef Parameters params);

        public native @Cast("bool") boolean run();
        public native void stop();
        public native void resetTracking();

        public native void process(@Const @ByRef Mat imageGray);

        public native @Cast("bool") boolean setParameters(@Const @ByRef Parameters params);
        public native @Const @ByRef Parameters getParameters();
        public native void getObjects(@ByRef RectVector result);
        public native void getObjects(@Cast("cv::DetectionBasedTracker::Object*") @StdVector IntIntPair result);

        /** enum cv::DetectionBasedTracker::ObjectStatus */
        public static final int
            DETECTED_NOT_SHOWN_YET = 0,
            DETECTED = 1,
            DETECTED_TEMPORARY_LOST = 2,
            WRONG_OBJECT = 3;
        @NoOffset public static class ExtObject extends Pointer {
            static { Loader.load(); }
            /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
            public ExtObject(Pointer p) { super(p); }
        
            public native int id(); public native ExtObject id(int setter);
            public native @ByRef Rect location(); public native ExtObject location(Rect setter);
            public native @Cast("cv::DetectionBasedTracker::ObjectStatus") int status(); public native ExtObject status(int setter);
            public ExtObject(int _id, @ByVal Rect _location, @Cast("cv::DetectionBasedTracker::ObjectStatus") int _status) { super((Pointer)null); allocate(_id, _location, _status); }
            private native void allocate(int _id, @ByVal Rect _location, @Cast("cv::DetectionBasedTracker::ObjectStatus") int _status);
        }
        public native void getObjects(@StdVector ExtObject result);


        public native int addObject(@Const @ByRef Rect location);
}