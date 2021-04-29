// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.cuda.nvml;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import org.bytedeco.cuda.cudart.*;
import static org.bytedeco.cuda.global.cudart.*;

import static org.bytedeco.cuda.global.nvml.*;


/** 
 * Description of HWBC entry 
 */
@Properties(inherit = org.bytedeco.cuda.presets.nvml.class)
public class nvmlHwbcEntry_t extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public nvmlHwbcEntry_t() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public nvmlHwbcEntry_t(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public nvmlHwbcEntry_t(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public nvmlHwbcEntry_t position(long position) {
        return (nvmlHwbcEntry_t)super.position(position);
    }
    @Override public nvmlHwbcEntry_t getPointer(long i) {
        return new nvmlHwbcEntry_t((Pointer)this).position(position + i);
    }

    public native @Cast("unsigned int") int hwbcId(); public native nvmlHwbcEntry_t hwbcId(int setter);
    public native @Cast("char") byte firmwareVersion(int i); public native nvmlHwbcEntry_t firmwareVersion(int i, byte setter);
    @MemberGetter public native @Cast("char*") BytePointer firmwareVersion();
}
