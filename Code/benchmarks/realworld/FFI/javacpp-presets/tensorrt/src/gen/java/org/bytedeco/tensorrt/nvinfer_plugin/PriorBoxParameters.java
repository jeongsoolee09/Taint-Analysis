// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.tensorrt.nvinfer_plugin;

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
import org.bytedeco.tensorrt.nvinfer.*;
import static org.bytedeco.tensorrt.global.nvinfer.*;

import static org.bytedeco.tensorrt.global.nvinfer_plugin.*;


/**
 *  \brief The PriorBox plugin layer generates the prior boxes of designated sizes and aspect ratios across all
 *  dimensions (H x W). PriorBoxParameters defines a set of parameters for creating the PriorBox plugin layer. It
 *  contains: @param minSize Minimum box size in pixels. Can not be nullptr. @param maxSize Maximum box size in pixels.
 *  Can be nullptr. @param aspectRatios Aspect ratios of the boxes. Can be nullptr. @param numMinSize Number of elements
 *  in minSize. Must be larger than 0. @param numMaxSize Number of elements in maxSize. Can be 0 or same as numMinSize.
 *  @param numAspectRatios Number of elements in aspectRatios. Can be 0.
 *  @param flip If true, will flip each aspect ratio. For example, if there is aspect ratio "r", the aspect ratio
 *  "1.0/r" will be generated as well. @param clip If true, will clip the prior so that it is within [0,1]. @param
 *  variance Variance for adjusting the prior boxes. @param imgH Image height. If 0, then the H dimension of the data
 *  tensor will be used. @param imgW Image width. If 0, then the W dimension of the data tensor will be used. @param
 *  stepH Step in H. If 0, then (float)imgH/h will be used where h is the H dimension of the 1st input tensor. @param
 *  stepW Step in W. If 0, then (float)imgW/w will be used where w is the W dimension of the 1st input tensor. @param
 *  offset Offset to the top left corner of each cell.
 *  */
@Namespace("nvinfer1::plugin") @Properties(inherit = org.bytedeco.tensorrt.presets.nvinfer_plugin.class)
public class PriorBoxParameters extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public PriorBoxParameters() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public PriorBoxParameters(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public PriorBoxParameters(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public PriorBoxParameters position(long position) {
        return (PriorBoxParameters)super.position(position);
    }
    @Override public PriorBoxParameters getPointer(long i) {
        return new PriorBoxParameters(this).position(position + i);
    }

    public native FloatPointer minSize(); public native PriorBoxParameters minSize(FloatPointer setter);
    public native FloatPointer maxSize(); public native PriorBoxParameters maxSize(FloatPointer setter);
    public native FloatPointer aspectRatios(); public native PriorBoxParameters aspectRatios(FloatPointer setter);
    public native int numMinSize(); public native PriorBoxParameters numMinSize(int setter);
    public native int numMaxSize(); public native PriorBoxParameters numMaxSize(int setter);
    public native int numAspectRatios(); public native PriorBoxParameters numAspectRatios(int setter);
    public native @Cast("bool") boolean flip(); public native PriorBoxParameters flip(boolean setter);
    public native @Cast("bool") boolean clip(); public native PriorBoxParameters clip(boolean setter);
    public native float variance(int i); public native PriorBoxParameters variance(int i, float setter);
    @MemberGetter public native FloatPointer variance();
    public native int imgH(); public native PriorBoxParameters imgH(int setter);
    public native int imgW(); public native PriorBoxParameters imgW(int setter);
    public native float stepH(); public native PriorBoxParameters stepH(float setter);
    public native float stepW(); public native PriorBoxParameters stepW(float setter);
    public native float offset(); public native PriorBoxParameters offset(float setter);
}
