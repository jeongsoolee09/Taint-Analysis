// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.opencv.opencv_core;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import static org.bytedeco.openblas.global.openblas_nolapack.*;
import static org.bytedeco.openblas.global.openblas.*;

import static org.bytedeco.opencv.global.opencv_core.*;


@Properties(inherit = org.bytedeco.opencv.presets.opencv_core.class)
public class IplConvKernel extends org.bytedeco.opencv.opencv_imgproc.AbstractIplConvKernel {
    static { Loader.load(); }
    /** Default native constructor. */
    public IplConvKernel() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public IplConvKernel(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public IplConvKernel(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public IplConvKernel position(long position) {
        return (IplConvKernel)super.position(position);
    }
    @Override public IplConvKernel getPointer(long i) {
        return new IplConvKernel(this).position(position + i);
    }

    public native int nCols(); public native IplConvKernel nCols(int setter);
    public native int nRows(); public native IplConvKernel nRows(int setter);
    public native int anchorX(); public native IplConvKernel anchorX(int setter);
    public native int anchorY(); public native IplConvKernel anchorY(int setter);
    public native IntPointer values(); public native IplConvKernel values(IntPointer setter);
    public native int nShiftR(); public native IplConvKernel nShiftR(int setter);
}
