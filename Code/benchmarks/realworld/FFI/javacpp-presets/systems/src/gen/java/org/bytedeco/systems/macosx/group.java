// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.systems.macosx;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.systems.global.macosx.*;

// #endif

@Properties(inherit = org.bytedeco.systems.presets.macosx.class)
public class group extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public group() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public group(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public group(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public group position(long position) {
        return (group)super.position(position);
    }
    @Override public group getPointer(long i) {
        return new group(this).position(position + i);
    }

	public native @Cast("char*") BytePointer gr_name(); public native group gr_name(BytePointer setter);		/* [XBD] group name */
	public native @Cast("char*") BytePointer gr_passwd(); public native group gr_passwd(BytePointer setter);		/* [???] group password */
	public native @Cast("gid_t") int gr_gid(); public native group gr_gid(int setter);			/* [XBD] group id */
	public native @Cast("char*") BytePointer gr_mem(int i); public native group gr_mem(int i, BytePointer setter);
	public native @Cast("char**") PointerPointer gr_mem(); public native group gr_mem(PointerPointer setter);		/* [XBD] group members */
}
