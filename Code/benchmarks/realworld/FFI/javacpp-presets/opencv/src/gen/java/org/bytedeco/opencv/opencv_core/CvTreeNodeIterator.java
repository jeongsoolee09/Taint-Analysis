// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.opencv.opencv_core;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import static org.bytedeco.openblas.global.openblas_nolapack.*;
import static org.bytedeco.openblas.global.openblas.*;

import static org.bytedeco.opencv.global.opencv_core.*;



/******************* Iteration through the sequence tree *****************/
@Properties(inherit = org.bytedeco.opencv.presets.opencv_core.class)
public class CvTreeNodeIterator extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public CvTreeNodeIterator() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public CvTreeNodeIterator(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public CvTreeNodeIterator(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public CvTreeNodeIterator position(long position) {
        return (CvTreeNodeIterator)super.position(position);
    }
    @Override public CvTreeNodeIterator getPointer(long i) {
        return new CvTreeNodeIterator(this).position(position + i);
    }

    public native @Const Pointer node(); public native CvTreeNodeIterator node(Pointer setter);
    public native int level(); public native CvTreeNodeIterator level(int setter);
    public native int max_level(); public native CvTreeNodeIterator max_level(int setter);
}
