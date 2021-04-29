// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.liquidfun;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.liquidfun.global.liquidfun.*;


/** Used for computing contact manifolds. */
@Properties(inherit = org.bytedeco.liquidfun.presets.liquidfun.class)
public class b2ClipVertex extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public b2ClipVertex() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public b2ClipVertex(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public b2ClipVertex(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public b2ClipVertex position(long position) {
        return (b2ClipVertex)super.position(position);
    }
    @Override public b2ClipVertex getPointer(long i) {
        return new b2ClipVertex(this).position(position + i);
    }

	public native @ByRef b2Vec2 v(); public native b2ClipVertex v(b2Vec2 setter);
	public native @ByRef b2ContactID id(); public native b2ClipVertex id(b2ContactID setter);
}