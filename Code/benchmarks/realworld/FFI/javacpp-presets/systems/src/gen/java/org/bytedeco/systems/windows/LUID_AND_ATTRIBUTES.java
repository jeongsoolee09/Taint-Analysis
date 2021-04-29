// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.systems.windows;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.systems.global.windows.*;


@Properties(inherit = org.bytedeco.systems.presets.windows.class)
public class LUID_AND_ATTRIBUTES extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public LUID_AND_ATTRIBUTES() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public LUID_AND_ATTRIBUTES(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public LUID_AND_ATTRIBUTES(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public LUID_AND_ATTRIBUTES position(long position) {
        return (LUID_AND_ATTRIBUTES)super.position(position);
    }
    @Override public LUID_AND_ATTRIBUTES getPointer(long i) {
        return new LUID_AND_ATTRIBUTES(this).position(position + i);
    }

    public native @ByRef LUID Luid(); public native LUID_AND_ATTRIBUTES Luid(LUID setter);
    public native @Cast("DWORD") int Attributes(); public native LUID_AND_ATTRIBUTES Attributes(int setter);
    }
