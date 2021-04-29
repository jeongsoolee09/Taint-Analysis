// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.liquidfun;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.liquidfun.global.liquidfun.*;


/** The pulley joint is connected to two bodies and two fixed ground points.
 *  The pulley supports a ratio such that:
 *  length1 + ratio * length2 <= constant
 *  Yes, the force transmitted is scaled by the ratio.
 *  Warning: the pulley joint can get a bit squirrelly by itself. They often
 *  work better when combined with prismatic joints. You should also cover the
 *  the anchor points with static shapes to prevent one side from going to
 *  zero length. */
@NoOffset @Properties(inherit = org.bytedeco.liquidfun.presets.liquidfun.class)
public class b2PulleyJoint extends b2Joint {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public b2PulleyJoint(Pointer p) { super(p); }

	public native @ByVal b2Vec2 GetAnchorA();
	public native @ByVal b2Vec2 GetAnchorB();

	public native @ByVal b2Vec2 GetReactionForce(@Cast("float32") float inv_dt);
	public native @Cast("float32") float GetReactionTorque(@Cast("float32") float inv_dt);

	/** Get the first ground anchor. */
	public native @ByVal b2Vec2 GetGroundAnchorA();

	/** Get the second ground anchor. */
	public native @ByVal b2Vec2 GetGroundAnchorB();

	/** Get the current length of the segment attached to bodyA. */
	public native @Cast("float32") float GetLengthA();

	/** Get the current length of the segment attached to bodyB. */
	public native @Cast("float32") float GetLengthB();

	/** Get the pulley ratio. */
	public native @Cast("float32") float GetRatio();

	/** Get the current length of the segment attached to bodyA. */
	public native @Cast("float32") float GetCurrentLengthA();

	/** Get the current length of the segment attached to bodyB. */
	public native @Cast("float32") float GetCurrentLengthB();

	/** Dump joint to dmLog */
	public native void Dump();

	/** Implement b2Joint::ShiftOrigin */
	public native void ShiftOrigin(@Const @ByRef b2Vec2 newOrigin);
}