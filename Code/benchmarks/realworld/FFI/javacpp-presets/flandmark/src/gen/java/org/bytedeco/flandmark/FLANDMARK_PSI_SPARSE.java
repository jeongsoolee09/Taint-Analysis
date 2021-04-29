// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.flandmark;

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

import static org.bytedeco.flandmark.global.flandmark.*;


@Properties(inherit = org.bytedeco.flandmark.presets.flandmark.class)
public class FLANDMARK_PSI_SPARSE extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public FLANDMARK_PSI_SPARSE() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public FLANDMARK_PSI_SPARSE(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public FLANDMARK_PSI_SPARSE(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public FLANDMARK_PSI_SPARSE position(long position) {
        return (FLANDMARK_PSI_SPARSE)super.position(position);
    }
    @Override public FLANDMARK_PSI_SPARSE getPointer(long i) {
        return new FLANDMARK_PSI_SPARSE(this).position(position + i);
    }

    public native @Cast("uint32_t*") IntPointer idxs(); public native FLANDMARK_PSI_SPARSE idxs(IntPointer setter);
    public native @Cast("uint32_t") int PSI_ROWS(); public native FLANDMARK_PSI_SPARSE PSI_ROWS(int setter);
    public native @Cast("uint32_t") int PSI_COLS(); public native FLANDMARK_PSI_SPARSE PSI_COLS(int setter);
}
