// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.liquidfun;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.liquidfun.global.liquidfun.*;


/** An axis aligned bounding box. */
@Properties(inherit = org.bytedeco.liquidfun.presets.liquidfun.class)
public class b2AABB extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public b2AABB() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public b2AABB(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public b2AABB(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public b2AABB position(long position) {
        return (b2AABB)super.position(position);
    }
    @Override public b2AABB getPointer(long i) {
        return new b2AABB(this).position(position + i);
    }

	/** Verify that the bounds are sorted. */
	public native @Cast("bool") boolean IsValid();

	/** Get the center of the AABB. */
	public native @ByVal b2Vec2 GetCenter();

	/** Get the extents of the AABB (half-widths). */
	public native @ByVal b2Vec2 GetExtents();

	/** Get the perimeter length */
	public native @Cast("float32") float GetPerimeter();

	/** Combine an AABB into this one. */
	public native void Combine(@Const @ByRef b2AABB aabb);

	/** Combine two AABBs into this one. */
	public native void Combine(@Const @ByRef b2AABB aabb1, @Const @ByRef b2AABB aabb2);

	/** Does this aabb contain the provided AABB. */
	public native @Cast("bool") boolean Contains(@Const @ByRef b2AABB aabb);

	public native @Cast("bool") boolean RayCast(b2RayCastOutput output, @Const @ByRef b2RayCastInput input);

	/** the lower vertex */
	public native @ByRef b2Vec2 lowerBound(); public native b2AABB lowerBound(b2Vec2 setter);
	/** the upper vertex */
	public native @ByRef b2Vec2 upperBound(); public native b2AABB upperBound(b2Vec2 setter);
}