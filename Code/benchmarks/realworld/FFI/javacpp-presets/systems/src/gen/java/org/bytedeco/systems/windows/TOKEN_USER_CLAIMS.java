// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.systems.windows;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.systems.global.windows.*;


@Properties(inherit = org.bytedeco.systems.presets.windows.class)
public class TOKEN_USER_CLAIMS extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public TOKEN_USER_CLAIMS() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public TOKEN_USER_CLAIMS(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public TOKEN_USER_CLAIMS(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public TOKEN_USER_CLAIMS position(long position) {
        return (TOKEN_USER_CLAIMS)super.position(position);
    }
    @Override public TOKEN_USER_CLAIMS getPointer(long i) {
        return new TOKEN_USER_CLAIMS(this).position(position + i);
    }

    public native @Cast("PCLAIMS_BLOB") Pointer UserClaims(); public native TOKEN_USER_CLAIMS UserClaims(Pointer setter);
}
