// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.liquidfun;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.liquidfun.global.liquidfun.*;


/** This is used to compute the current state of a contact manifold. */
@Properties(inherit = org.bytedeco.liquidfun.presets.liquidfun.class)
public class b2WorldManifold extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public b2WorldManifold() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public b2WorldManifold(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public b2WorldManifold(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public b2WorldManifold position(long position) {
        return (b2WorldManifold)super.position(position);
    }
    @Override public b2WorldManifold getPointer(long i) {
        return new b2WorldManifold(this).position(position + i);
    }

	/** Evaluate the manifold with supplied transforms. This assumes
	 *  modest motion from the original state. This does not change the
	 *  point count, impulses, etc. The radii must come from the shapes
	 *  that generated the manifold. */
	public native void Initialize(@Const b2Manifold manifold,
						@Const @ByRef b2Transform xfA, @Cast("float32") float radiusA,
						@Const @ByRef b2Transform xfB, @Cast("float32") float radiusB);

	/** world vector pointing from A to B */
	public native @ByRef b2Vec2 normal(); public native b2WorldManifold normal(b2Vec2 setter);
	/** world contact point (point of intersection) */
	public native @ByRef b2Vec2 points(int i); public native b2WorldManifold points(int i, b2Vec2 setter);
	@MemberGetter public native b2Vec2 points();
	/** a negative value indicates overlap, in meters */
	public native @Cast("float32") float separations(int i); public native b2WorldManifold separations(int i, float setter);
	@MemberGetter public native @Cast("float32*") FloatPointer separations();
}