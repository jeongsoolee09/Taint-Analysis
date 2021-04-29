// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.systems.linux;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.systems.global.linux.*;

// #endif
// #if defined __USE_ISOC99 && !defined __lldiv_t_defined
/* Returned by `lldiv'.  */
@Properties(inherit = org.bytedeco.systems.presets.linux.class)
public class lldiv_t extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public lldiv_t() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public lldiv_t(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public lldiv_t(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public lldiv_t position(long position) {
        return (lldiv_t)super.position(position);
    }
    @Override public lldiv_t getPointer(long i) {
        return new lldiv_t(this).position(position + i);
    }

    public native long quot(); public native lldiv_t quot(long setter);		/* Quotient.  */
    public native long rem(); public native lldiv_t rem(long setter);		/* Remainder.  */
  }