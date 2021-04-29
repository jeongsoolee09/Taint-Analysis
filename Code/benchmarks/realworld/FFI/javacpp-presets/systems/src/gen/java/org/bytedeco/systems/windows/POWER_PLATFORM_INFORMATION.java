// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.systems.windows;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.systems.global.windows.*;


// #endif

@Properties(inherit = org.bytedeco.systems.presets.windows.class)
public class POWER_PLATFORM_INFORMATION extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public POWER_PLATFORM_INFORMATION() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public POWER_PLATFORM_INFORMATION(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public POWER_PLATFORM_INFORMATION(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public POWER_PLATFORM_INFORMATION position(long position) {
        return (POWER_PLATFORM_INFORMATION)super.position(position);
    }
    @Override public POWER_PLATFORM_INFORMATION getPointer(long i) {
        return new POWER_PLATFORM_INFORMATION(this).position(position + i);
    }

    public native @Cast("BOOLEAN") boolean AoAc(); public native POWER_PLATFORM_INFORMATION AoAc(boolean setter);
}