// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.hdf5;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.hdf5.global.hdf5.*;


/** \class FileCreatPropList
    \brief Class FileCreatPropList inherits from PropList and provides
    wrappers for the HDF5 file create property list.
*/
//  Inheritance: PropList -> IdComponent
@Namespace("H5") @NoOffset @Properties(inherit = org.bytedeco.hdf5.presets.hdf5.class)
public class FileCreatPropList extends PropList {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public FileCreatPropList(Pointer p) { super(p); }

        /**\brief Default file creation property list. */
        @MemberGetter public static native @Const @ByRef FileCreatPropList DEFAULT();

        // Creates a file create property list.
        public FileCreatPropList() { super((Pointer)null); allocate(); }
        private native void allocate();

// #ifndef H5_NO_DEPRECATED_SYMBOLS
// #endif /* H5_NO_DEPRECATED_SYMBOLS */

        // Sets the userblock size field of a file creation property list.
        public native void setUserblock(@Cast("hsize_t") long size);

        // Gets the size of a user block in this file creation property list.
        public native @Cast("hsize_t") long getUserblock();

        // Retrieves the size-of address and size quantities stored in a
        // file according to this file creation property list.
        public native void getSizes(@Cast("size_t*") @ByRef SizeTPointer sizeof_addr, @Cast("size_t*") @ByRef SizeTPointer sizeof_size);

        // Sets file size-of addresses and sizes.
        public native void setSizes(@Cast("size_t") long sizeof_addr/*=4*/, @Cast("size_t") long sizeof_size/*=4*/);
        public native void setSizes();

        // Retrieves the size of the symbol table B-tree 1/2 rank and the
        // symbol table leaf node 1/2 size.
        public native void getSymk(@Cast("unsigned*") @ByRef IntPointer int_nodes_k, @Cast("unsigned*") @ByRef IntPointer leaf_nodes_k);
        public native void getSymk(@Cast("unsigned*") @ByRef IntBuffer int_nodes_k, @Cast("unsigned*") @ByRef IntBuffer leaf_nodes_k);
        public native void getSymk(@Cast("unsigned*") @ByRef int[] int_nodes_k, @Cast("unsigned*") @ByRef int[] leaf_nodes_k);

        // Sets the size of parameters used to control the symbol table nodes.
        public native void setSymk(@Cast("unsigned") int int_nodes_k, @Cast("unsigned") int leaf_nodes_k);

        // Returns the 1/2 rank of an indexed storage B-tree.
        public native @Cast("unsigned") int getIstorek();

        // Sets the size of parameter used to control the B-trees for
        // indexing chunked datasets.
        public native void setIstorek(@Cast("unsigned") int ik);

        // Sets the strategy and the threshold value that the library will
        // will employ in managing file space.
        public native void setFileSpaceStrategy(@Cast("H5F_fspace_strategy_t") int strategy, @Cast("hbool_t") boolean persist, @Cast("hsize_t") long threshold);

        // Returns the strategy that the library uses in managing file space.
        public native void getFileSpaceStrategy(@Cast("H5F_fspace_strategy_t*") @ByRef IntPointer strategy, @Cast("hbool_t*") @ByRef BoolPointer persist, @Cast("hsize_t*") @ByRef LongPointer threshold);
        public native void getFileSpaceStrategy(@Cast("H5F_fspace_strategy_t*") @ByRef IntBuffer strategy, @Cast("hbool_t*") @ByRef boolean[] persist, @Cast("hsize_t*") @ByRef LongBuffer threshold);
        public native void getFileSpaceStrategy(@Cast("H5F_fspace_strategy_t*") @ByRef int[] strategy, @Cast("hbool_t*") @ByRef BoolPointer persist, @Cast("hsize_t*") @ByRef long[] threshold);
        public native void getFileSpaceStrategy(@Cast("H5F_fspace_strategy_t*") @ByRef IntPointer strategy, @Cast("hbool_t*") @ByRef boolean[] persist, @Cast("hsize_t*") @ByRef LongPointer threshold);
        public native void getFileSpaceStrategy(@Cast("H5F_fspace_strategy_t*") @ByRef IntBuffer strategy, @Cast("hbool_t*") @ByRef BoolPointer persist, @Cast("hsize_t*") @ByRef LongBuffer threshold);
        public native void getFileSpaceStrategy(@Cast("H5F_fspace_strategy_t*") @ByRef int[] strategy, @Cast("hbool_t*") @ByRef boolean[] persist, @Cast("hsize_t*") @ByRef long[] threshold);

        // Sets the file space page size for paged aggregation.
        public native void setFileSpacePagesize(@Cast("hsize_t") long fsp_psize);

        // Returns the threshold value that the library uses in tracking free
        // space sections.
        public native @Cast("hsize_t") long getFileSpacePagesize();

        /**\brief Returns this class name. */
        public native @StdString BytePointer fromClass();

        // Copy constructor: same as the original FileCreatPropList.
        public FileCreatPropList(@Const @ByRef FileCreatPropList orig) { super((Pointer)null); allocate(orig); }
        private native void allocate(@Const @ByRef FileCreatPropList orig);

        // Creates a copy of an existing file create property list
        // using the property list id.
        public FileCreatPropList(@Cast("const hid_t") long plist_id) { super((Pointer)null); allocate(plist_id); }
        private native void allocate(@Cast("const hid_t") long plist_id);

        // Noop destructor

// #ifndef DOXYGEN_SHOULD_SKIP_THIS

        // Deletes the global constant, should only be used by the library
        public static native void deleteConstants();

}