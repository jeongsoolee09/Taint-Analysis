// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.tensorflow;

import org.bytedeco.tensorflow.Allocator;
import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.tensorflow.global.tensorflow.*;

@Name("std::unordered_map<int,std::pair<tensorflow::DataType,tensorflow::TensorShape> >") @Properties(inherit = org.bytedeco.tensorflow.presets.tensorflow.class)
public class IntDataTypeTensorShapePairMap extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public IntDataTypeTensorShapePairMap(Pointer p) { super(p); }
    public IntDataTypeTensorShapePairMap()       { allocate();  }
    private native void allocate();
    public native @Name("operator =") @ByRef IntDataTypeTensorShapePairMap put(@ByRef IntDataTypeTensorShapePairMap x);

    public boolean empty() { return size() == 0; }
    public native long size();

    @Index(function = "at") public native @Cast("tensorflow::DataType") int first(int i); public native IntDataTypeTensorShapePairMap first(int i, int first);
    @Index(function = "at") public native @ByRef TensorShape second(int i);  public native IntDataTypeTensorShapePairMap second(int i, TensorShape second);
}

