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
 * Fan speed readings for an entire S-class unit.
 */
@Properties(inherit = org.bytedeco.cuda.presets.nvml.class)
public class nvmlUnitFanSpeeds_t extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public nvmlUnitFanSpeeds_t() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public nvmlUnitFanSpeeds_t(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public nvmlUnitFanSpeeds_t(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public nvmlUnitFanSpeeds_t position(long position) {
        return (nvmlUnitFanSpeeds_t)super.position(position);
    }
    @Override public nvmlUnitFanSpeeds_t getPointer(long i) {
        return new nvmlUnitFanSpeeds_t((Pointer)this).position(position + i);
    }

    /** Fan speed data for each fan */
    public native @ByRef nvmlUnitFanInfo_t fans(int i); public native nvmlUnitFanSpeeds_t fans(int i, nvmlUnitFanInfo_t setter);
    @MemberGetter public native nvmlUnitFanInfo_t fans();
    /** Number of fans in unit */
    public native @Cast("unsigned int") int count(); public native nvmlUnitFanSpeeds_t count(int setter);
}
