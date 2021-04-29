// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.leptonica;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.leptonica.global.lept.*;


/**
 * \file list.h
 *
 * <pre>
 *       Cell for double-linked lists
 *
 *       This allows composition of a list of cells with
 *           prev, next and data pointers.  Generic data
 *           structures hang on the list cell data pointers.
 *
 *       The list is not circular because that would add much
 *           complexity in traversing the list under general
 *           conditions where list cells can be added and removed.
 *           The only disadvantage of not having the head point to
 *           the last cell is that the list must be traversed to
 *           find its tail.  However, this traversal is fast, and
 *           the listRemoveFromTail() function updates the tail
 *           so there is no searching overhead with repeated use.
 *
 *       The list macros are used to run through a list, and their
 *       use is encouraged.  They are invoked, e.g., as
 *
 *             DLLIST  *head, *elem;
 *             ...
 *             L_BEGIN_LIST_FORWARD(head, elem)
 *                 <do something with elem and/or elem->data >
 *             L_END_LIST
 * </pre>
 */

@Name("DoubleLinkedList") @Properties(inherit = org.bytedeco.leptonica.presets.lept.class)
public class DLLIST extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public DLLIST() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public DLLIST(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public DLLIST(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public DLLIST position(long position) {
        return (DLLIST)super.position(position);
    }
    @Override public DLLIST getPointer(long i) {
        return new DLLIST(this).position(position + i);
    }

    public native DLLIST prev(); public native DLLIST prev(DLLIST setter);
    public native DLLIST next(); public native DLLIST next(DLLIST setter);
    public native Pointer data(); public native DLLIST data(Pointer setter);
}