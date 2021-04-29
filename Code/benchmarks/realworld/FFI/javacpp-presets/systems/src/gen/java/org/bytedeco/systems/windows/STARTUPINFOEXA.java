// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.systems.windows;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.systems.global.windows.*;

// #endif /* WINVER >= 0x0400 */

// #if (_WIN32_WINNT >= 0x0600)

@Properties(inherit = org.bytedeco.systems.presets.windows.class)
public class STARTUPINFOEXA extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public STARTUPINFOEXA() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public STARTUPINFOEXA(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public STARTUPINFOEXA(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public STARTUPINFOEXA position(long position) {
        return (STARTUPINFOEXA)super.position(position);
    }
    @Override public STARTUPINFOEXA getPointer(long i) {
        return new STARTUPINFOEXA(this).position(position + i);
    }

    public native @ByRef STARTUPINFOA StartupInfo(); public native STARTUPINFOEXA StartupInfo(STARTUPINFOA setter);
    public native _PROC_THREAD_ATTRIBUTE_LIST lpAttributeList(); public native STARTUPINFOEXA lpAttributeList(_PROC_THREAD_ATTRIBUTE_LIST setter);
}