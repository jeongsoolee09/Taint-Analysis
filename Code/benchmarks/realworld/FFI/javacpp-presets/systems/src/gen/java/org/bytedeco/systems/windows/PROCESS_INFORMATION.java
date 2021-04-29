// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.systems.windows;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.systems.global.windows.*;


// #if WINAPI_FAMILY_PARTITION(WINAPI_PARTITION_DESKTOP)

@Properties(inherit = org.bytedeco.systems.presets.windows.class)
public class PROCESS_INFORMATION extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public PROCESS_INFORMATION() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public PROCESS_INFORMATION(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public PROCESS_INFORMATION(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public PROCESS_INFORMATION position(long position) {
        return (PROCESS_INFORMATION)super.position(position);
    }
    @Override public PROCESS_INFORMATION getPointer(long i) {
        return new PROCESS_INFORMATION(this).position(position + i);
    }

    public native @Cast("HANDLE") Pointer hProcess(); public native PROCESS_INFORMATION hProcess(Pointer setter);
    public native @Cast("HANDLE") Pointer hThread(); public native PROCESS_INFORMATION hThread(Pointer setter);
    public native @Cast("DWORD") int dwProcessId(); public native PROCESS_INFORMATION dwProcessId(int setter);
    public native @Cast("DWORD") int dwThreadId(); public native PROCESS_INFORMATION dwThreadId(int setter);
}
