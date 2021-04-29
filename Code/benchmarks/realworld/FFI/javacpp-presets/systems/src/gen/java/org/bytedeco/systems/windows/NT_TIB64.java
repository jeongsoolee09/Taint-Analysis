// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.systems.windows;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.systems.global.windows.*;


@Properties(inherit = org.bytedeco.systems.presets.windows.class)
public class NT_TIB64 extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public NT_TIB64() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public NT_TIB64(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public NT_TIB64(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public NT_TIB64 position(long position) {
        return (NT_TIB64)super.position(position);
    }
    @Override public NT_TIB64 getPointer(long i) {
        return new NT_TIB64(this).position(position + i);
    }

    public native @Cast("DWORD64") long ExceptionList(); public native NT_TIB64 ExceptionList(long setter);
    public native @Cast("DWORD64") long StackBase(); public native NT_TIB64 StackBase(long setter);
    public native @Cast("DWORD64") long StackLimit(); public native NT_TIB64 StackLimit(long setter);
    public native @Cast("DWORD64") long SubSystemTib(); public native NT_TIB64 SubSystemTib(long setter);

// #if defined(_MSC_EXTENSIONS)
        public native @Cast("DWORD64") long FiberData(); public native NT_TIB64 FiberData(long setter);
        public native @Cast("DWORD") int Version(); public native NT_TIB64 Version(int setter);

// #else
// #endif

    public native @Cast("DWORD64") long ArbitraryUserPointer(); public native NT_TIB64 ArbitraryUserPointer(long setter);
    public native @Cast("DWORD64") long Self(); public native NT_TIB64 Self(long setter);
}
