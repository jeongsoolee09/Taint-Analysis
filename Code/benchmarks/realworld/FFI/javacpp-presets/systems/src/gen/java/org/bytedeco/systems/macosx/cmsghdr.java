// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.systems.macosx;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.systems.global.macosx.*;
         /* do not generate SIGPIPE on EOF */
// #endif /* __DARWIN_C_LEVEL */

// #if !defined(_POSIX_C_SOURCE) || defined(_DARWIN_C_SOURCE)
// #endif  /* (!_POSIX_C_SOURCE || _DARWIN_C_SOURCE) */

/*
 * Header for ancillary data objects in msg_control buffer.
 * Used for additional information with/about a datagram
 * not expressible by flags.  The format is a sequence
 * of message elements headed by cmsghdr structures.
 */
@Properties(inherit = org.bytedeco.systems.presets.macosx.class)
public class cmsghdr extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public cmsghdr() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public cmsghdr(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public cmsghdr(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public cmsghdr position(long position) {
        return (cmsghdr)super.position(position);
    }
    @Override public cmsghdr getPointer(long i) {
        return new cmsghdr(this).position(position + i);
    }

	public native @Cast("socklen_t") int cmsg_len(); public native cmsghdr cmsg_len(int setter);       /* [XSI] data byte count, including hdr */
	public native int cmsg_level(); public native cmsghdr cmsg_level(int setter);     /* [XSI] originating protocol */
	public native int cmsg_type(); public native cmsghdr cmsg_type(int setter);      /* [XSI] protocol-specific type */
/* followed by	unsigned char  cmsg_data[]; */
}