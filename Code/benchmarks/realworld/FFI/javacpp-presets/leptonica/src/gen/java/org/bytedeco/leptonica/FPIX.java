// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.leptonica;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.leptonica.global.lept.*;


/** Pix with float array */
@Name("FPix") @Properties(inherit = org.bytedeco.leptonica.presets.lept.class)
public class FPIX extends AbstractFPIX {
    static { Loader.load(); }
    /** Default native constructor. */
    public FPIX() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public FPIX(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public FPIX(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public FPIX position(long position) {
        return (FPIX)super.position(position);
    }
    @Override public FPIX getPointer(long i) {
        return new FPIX(this).position(position + i);
    }

    /** width in pixels                   */
    public native @Cast("l_int32") int w(); public native FPIX w(int setter);
    /** height in pixels                  */
    public native @Cast("l_int32") int h(); public native FPIX h(int setter);
    /** 32-bit words/line                 */
    public native @Cast("l_int32") int wpl(); public native FPIX wpl(int setter);
    /** reference count (1 if no clones)  */
    public native @Cast("l_uint32") int refcount(); public native FPIX refcount(int setter);
    /** image res (ppi) in x direction    */
    /** (use 0 if unknown)                */
    public native @Cast("l_int32") int xres(); public native FPIX xres(int setter);
    /** image res (ppi) in y direction    */
    /** (use 0 if unknown)                */
    public native @Cast("l_int32") int yres(); public native FPIX yres(int setter);
    /** the float image data              */
    public native @Cast("l_float32*") FloatPointer data(); public native FPIX data(FloatPointer setter);
}
