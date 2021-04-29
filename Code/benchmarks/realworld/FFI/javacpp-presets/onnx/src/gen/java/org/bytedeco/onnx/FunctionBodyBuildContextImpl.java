// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.onnx;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.onnx.global.onnx.*;


@Namespace("onnx") @NoOffset @Properties(inherit = org.bytedeco.onnx.presets.onnx.class)
public class FunctionBodyBuildContextImpl extends FunctionBodyBuildContext {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public FunctionBodyBuildContextImpl(Pointer p) { super(p); }

  public FunctionBodyBuildContextImpl(@ByRef NodeProto node_proto) { super((Pointer)null); allocate(node_proto); }
  private native void allocate(@ByRef NodeProto node_proto);

  public native @Const AttributeProto getAttribute(@StdString BytePointer name);
  public native @Const AttributeProto getAttribute(@StdString String name);

  public native @Cast("bool") boolean hasInput(int i);

  public native @Cast("bool") boolean hasOutput(int i);

  public native @ByRef StringAttributeProtoMap attributesByName_(); public native FunctionBodyBuildContextImpl attributesByName_(StringAttributeProtoMap setter);

  public native @ByRef NodeProto node_proto_(); public native FunctionBodyBuildContextImpl node_proto_(NodeProto setter);
}