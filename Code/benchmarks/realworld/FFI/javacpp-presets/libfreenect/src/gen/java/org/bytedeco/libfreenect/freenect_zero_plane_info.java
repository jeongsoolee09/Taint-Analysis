// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.libfreenect;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.libfreenect.global.freenect.*;


/** internal Kinect zero plane data */
@Properties(inherit = org.bytedeco.libfreenect.presets.freenect.class)
public class freenect_zero_plane_info extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public freenect_zero_plane_info() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public freenect_zero_plane_info(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public freenect_zero_plane_info(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public freenect_zero_plane_info position(long position) {
        return (freenect_zero_plane_info)super.position(position);
    }
    @Override public freenect_zero_plane_info getPointer(long i) {
        return new freenect_zero_plane_info(this).position(position + i);
    }

	public native float dcmos_emitter_dist(); public native freenect_zero_plane_info dcmos_emitter_dist(float setter);    // Distance between IR camera and IR emitter, in cm.
	public native float dcmos_rcmos_dist(); public native freenect_zero_plane_info dcmos_rcmos_dist(float setter);      // Distance between IR camera and RGB camera, in cm.
	public native float reference_distance(); public native freenect_zero_plane_info reference_distance(float setter);    // The focal length of the IR camera, in mm.
	public native float reference_pixel_size(); public native freenect_zero_plane_info reference_pixel_size(float setter);  // The size of a single pixel on the zero plane, in mm.
}
