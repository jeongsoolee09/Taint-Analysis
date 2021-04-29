// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.tensorrt.nvinfer;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import org.bytedeco.cuda.cudart.*;
import static org.bytedeco.cuda.global.cudart.*;
import org.bytedeco.cuda.cublas.*;
import static org.bytedeco.cuda.global.cublas.*;
import org.bytedeco.cuda.cudnn.*;
import static org.bytedeco.cuda.global.cudnn.*;
import org.bytedeco.cuda.nvrtc.*;
import static org.bytedeco.cuda.global.nvrtc.*;

import static org.bytedeco.tensorrt.global.nvinfer.*;


@Namespace("nvinfer1") @Properties(inherit = org.bytedeco.tensorrt.presets.nvinfer.class)
public class IIteratorLayer extends ILoopBoundaryLayer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public IIteratorLayer(Pointer p) { super(p); }

    /** Set axis to iterate over. */
    public native @NoException void setAxis(int axis);

    /** Get axis being iterated over. */
    public native @NoException int getAxis();

    /** For reverse=false, the layer is equivalent to addGather(tensor, I, 0) where I is a
     *  scalar tensor containing the loop iteration number.
     *  For reverse=true, the layer is equivalent to addGather(tensor, M-1-I, 0) where M is the trip count
     *  computed from TripLimits of kind kCOUNT.
     *  The default is reverse=false. */
    public native @NoException void setReverse(@Cast("bool") boolean reverse);

    /** True if and only if reversing input. */
    public native @Cast("bool") @NoException boolean getReverse();
}
