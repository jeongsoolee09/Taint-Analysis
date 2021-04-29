// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.tensorflow;

import org.bytedeco.tensorflow.Allocator;
import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.tensorflow.global.tensorflow.*;

// -------------------------------------------------------------------

@Namespace("tensorflow") @NoOffset @Properties(inherit = org.bytedeco.tensorflow.presets.tensorflow.class)
public class NodeExecStats extends MessageLite {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public NodeExecStats(Pointer p) { super(p); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public NodeExecStats(long size) { super((Pointer)null); allocateArray(size); }
    private native void allocateArray(long size);
    @Override public NodeExecStats position(long position) {
        return (NodeExecStats)super.position(position);
    }
    @Override public NodeExecStats getPointer(long i) {
        return new NodeExecStats(this).position(position + i);
    }

  public NodeExecStats() { super((Pointer)null); allocate(); }
  private native void allocate();

  public NodeExecStats(@Const @ByRef NodeExecStats from) { super((Pointer)null); allocate(from); }
  private native void allocate(@Const @ByRef NodeExecStats from);

  public native @ByRef @Name("operator =") NodeExecStats put(@Const @ByRef NodeExecStats from);

  public native Arena GetArena();
  public native Pointer GetMaybeArenaPointer();
  public static native @Cast("const google::protobuf::Descriptor*") Pointer descriptor();
  public static native @Cast("const google::protobuf::Descriptor*") Pointer GetDescriptor();
  public static native @Cast("const google::protobuf::Reflection*") Pointer GetReflection();
  public static native @Const @ByRef NodeExecStats default_instance();

  public static native void InitAsDefaultInstance();  // FOR INTERNAL USE ONLY
  public static native @Const NodeExecStats internal_default_instance();
  @MemberGetter public static native int kIndexInFileMessages();
  public static final int kIndexInFileMessages = kIndexInFileMessages();

  public native void UnsafeArenaSwap(NodeExecStats other);
  public native void Swap(NodeExecStats other);
  

  // implements Message ----------------------------------------------

  public native NodeExecStats New();

  public native NodeExecStats New(Arena arena);
  public native void CopyFrom(@Cast("const google::protobuf::Message*") @ByRef MessageLite from);
  public native void MergeFrom(@Cast("const google::protobuf::Message*") @ByRef MessageLite from);
  public native void CopyFrom(@Const @ByRef NodeExecStats from);
  public native void MergeFrom(@Const @ByRef NodeExecStats from);
  public native void Clear();
  public native @Cast("bool") boolean IsInitialized();

  public native @Cast("size_t") long ByteSizeLong();
//   #if GOOGLE_PROTOBUF_ENABLE_EXPERIMENTAL_PARSER
//   #else
  public native @Cast("bool") boolean MergePartialFromCodedStream(
        CodedInputStream input);
//   #endif  // GOOGLE_PROTOBUF_ENABLE_EXPERIMENTAL_PARSER
  public native void SerializeWithCachedSizes(
        CodedOutputStream output);
  public native @Cast("google::protobuf::uint8*") BytePointer InternalSerializeWithCachedSizesToArray(
        @Cast("google::protobuf::uint8*") BytePointer target);
  public native @Cast("google::protobuf::uint8*") ByteBuffer InternalSerializeWithCachedSizesToArray(
        @Cast("google::protobuf::uint8*") ByteBuffer target);
  public native @Cast("google::protobuf::uint8*") byte[] InternalSerializeWithCachedSizesToArray(
        @Cast("google::protobuf::uint8*") byte[] target);
  public native int GetCachedSize();

  public native @ByVal @Cast("google::protobuf::Metadata*") Pointer GetMetadata();

  // nested types ----------------------------------------------------

  // accessors -------------------------------------------------------

  // repeated .tensorflow.AllocatorMemoryUsed memory = 6;
  public native int memory_size();
  public native void clear_memory();
  @MemberGetter public static native int kMemoryFieldNumber();
  public static final int kMemoryFieldNumber = kMemoryFieldNumber();
  public native AllocatorMemoryUsed mutable_memory(int index);
  public native @Const @ByRef AllocatorMemoryUsed memory(int index);
  public native AllocatorMemoryUsed add_memory();

  // repeated .tensorflow.NodeOutput output = 7;
  public native int output_size();
  public native void clear_output();
  @MemberGetter public static native int kOutputFieldNumber();
  public static final int kOutputFieldNumber = kOutputFieldNumber();
  public native NodeOutput mutable_output(int index);
  public native @Const @ByRef NodeOutput output(int index);
  public native NodeOutput add_output();

  // repeated .tensorflow.AllocationDescription referenced_tensor = 11;
  public native int referenced_tensor_size();
  public native void clear_referenced_tensor();
  @MemberGetter public static native int kReferencedTensorFieldNumber();
  public static final int kReferencedTensorFieldNumber = kReferencedTensorFieldNumber();
  public native AllocationDescription mutable_referenced_tensor(int index);
  public native @Const @ByRef AllocationDescription referenced_tensor(int index);
  public native AllocationDescription add_referenced_tensor();

  // string node_name = 1;
  public native void clear_node_name();
  @MemberGetter public static native int kNodeNameFieldNumber();
  public static final int kNodeNameFieldNumber = kNodeNameFieldNumber();
  public native @StdString BytePointer node_name();
  public native void set_node_name(@StdString BytePointer value);
  public native void set_node_name(@StdString String value);
  public native void set_node_name(@Cast("const char*") BytePointer value, @Cast("size_t") long size);
  public native void set_node_name(String value, @Cast("size_t") long size);
  public native @StdString @Cast({"char*", "std::string*"}) BytePointer mutable_node_name();
  public native @StdString @Cast({"char*", "std::string*"}) BytePointer release_node_name();
  public native void set_allocated_node_name(@StdString @Cast({"char*", "std::string*"}) BytePointer node_name);
  public native @StdString @Cast({"char*", "std::string*"}) BytePointer unsafe_arena_release_node_name();
  public native void unsafe_arena_set_allocated_node_name(
        @StdString @Cast({"char*", "std::string*"}) BytePointer node_name);

  // string timeline_label = 8;
  public native void clear_timeline_label();
  @MemberGetter public static native int kTimelineLabelFieldNumber();
  public static final int kTimelineLabelFieldNumber = kTimelineLabelFieldNumber();
  public native @StdString BytePointer timeline_label();
  public native void set_timeline_label(@StdString BytePointer value);
  public native void set_timeline_label(@StdString String value);
  public native void set_timeline_label(@Cast("const char*") BytePointer value, @Cast("size_t") long size);
  public native void set_timeline_label(String value, @Cast("size_t") long size);
  public native @StdString @Cast({"char*", "std::string*"}) BytePointer mutable_timeline_label();
  public native @StdString @Cast({"char*", "std::string*"}) BytePointer release_timeline_label();
  public native void set_allocated_timeline_label(@StdString @Cast({"char*", "std::string*"}) BytePointer timeline_label);
  public native @StdString @Cast({"char*", "std::string*"}) BytePointer unsafe_arena_release_timeline_label();
  public native void unsafe_arena_set_allocated_timeline_label(
        @StdString @Cast({"char*", "std::string*"}) BytePointer timeline_label);

  // .tensorflow.MemoryStats memory_stats = 12;
  public native @Cast("bool") boolean has_memory_stats();
  public native void clear_memory_stats();
  @MemberGetter public static native int kMemoryStatsFieldNumber();
  public static final int kMemoryStatsFieldNumber = kMemoryStatsFieldNumber();
  public native @Const @ByRef MemoryStats memory_stats();
  public native MemoryStats release_memory_stats();
  public native MemoryStats mutable_memory_stats();
  public native void set_allocated_memory_stats(MemoryStats memory_stats);
  public native void unsafe_arena_set_allocated_memory_stats(
        MemoryStats memory_stats);
  public native MemoryStats unsafe_arena_release_memory_stats();

  // int64 all_start_micros = 2;
  public native void clear_all_start_micros();
  @MemberGetter public static native int kAllStartMicrosFieldNumber();
  public static final int kAllStartMicrosFieldNumber = kAllStartMicrosFieldNumber();
  public native @Cast("google::protobuf::int64") long all_start_micros();
  public native void set_all_start_micros(@Cast("google::protobuf::int64") long value);

  // int64 op_start_rel_micros = 3;
  public native void clear_op_start_rel_micros();
  @MemberGetter public static native int kOpStartRelMicrosFieldNumber();
  public static final int kOpStartRelMicrosFieldNumber = kOpStartRelMicrosFieldNumber();
  public native @Cast("google::protobuf::int64") long op_start_rel_micros();
  public native void set_op_start_rel_micros(@Cast("google::protobuf::int64") long value);

  // int64 op_end_rel_micros = 4;
  public native void clear_op_end_rel_micros();
  @MemberGetter public static native int kOpEndRelMicrosFieldNumber();
  public static final int kOpEndRelMicrosFieldNumber = kOpEndRelMicrosFieldNumber();
  public native @Cast("google::protobuf::int64") long op_end_rel_micros();
  public native void set_op_end_rel_micros(@Cast("google::protobuf::int64") long value);

  // int64 all_end_rel_micros = 5;
  public native void clear_all_end_rel_micros();
  @MemberGetter public static native int kAllEndRelMicrosFieldNumber();
  public static final int kAllEndRelMicrosFieldNumber = kAllEndRelMicrosFieldNumber();
  public native @Cast("google::protobuf::int64") long all_end_rel_micros();
  public native void set_all_end_rel_micros(@Cast("google::protobuf::int64") long value);

  // int64 scheduled_micros = 9;
  public native void clear_scheduled_micros();
  @MemberGetter public static native int kScheduledMicrosFieldNumber();
  public static final int kScheduledMicrosFieldNumber = kScheduledMicrosFieldNumber();
  public native @Cast("google::protobuf::int64") long scheduled_micros();
  public native void set_scheduled_micros(@Cast("google::protobuf::int64") long value);

  // int64 all_start_nanos = 13;
  public native void clear_all_start_nanos();
  @MemberGetter public static native int kAllStartNanosFieldNumber();
  public static final int kAllStartNanosFieldNumber = kAllStartNanosFieldNumber();
  public native @Cast("google::protobuf::int64") long all_start_nanos();
  public native void set_all_start_nanos(@Cast("google::protobuf::int64") long value);

  // int64 op_start_rel_nanos = 14;
  public native void clear_op_start_rel_nanos();
  @MemberGetter public static native int kOpStartRelNanosFieldNumber();
  public static final int kOpStartRelNanosFieldNumber = kOpStartRelNanosFieldNumber();
  public native @Cast("google::protobuf::int64") long op_start_rel_nanos();
  public native void set_op_start_rel_nanos(@Cast("google::protobuf::int64") long value);

  // int64 op_end_rel_nanos = 15;
  public native void clear_op_end_rel_nanos();
  @MemberGetter public static native int kOpEndRelNanosFieldNumber();
  public static final int kOpEndRelNanosFieldNumber = kOpEndRelNanosFieldNumber();
  public native @Cast("google::protobuf::int64") long op_end_rel_nanos();
  public native void set_op_end_rel_nanos(@Cast("google::protobuf::int64") long value);

  // int64 all_end_rel_nanos = 16;
  public native void clear_all_end_rel_nanos();
  @MemberGetter public static native int kAllEndRelNanosFieldNumber();
  public static final int kAllEndRelNanosFieldNumber = kAllEndRelNanosFieldNumber();
  public native @Cast("google::protobuf::int64") long all_end_rel_nanos();
  public native void set_all_end_rel_nanos(@Cast("google::protobuf::int64") long value);

  // int64 scheduled_nanos = 17;
  public native void clear_scheduled_nanos();
  @MemberGetter public static native int kScheduledNanosFieldNumber();
  public static final int kScheduledNanosFieldNumber = kScheduledNanosFieldNumber();
  public native @Cast("google::protobuf::int64") long scheduled_nanos();
  public native void set_scheduled_nanos(@Cast("google::protobuf::int64") long value);

  // uint32 thread_id = 10;
  public native void clear_thread_id();
  @MemberGetter public static native int kThreadIdFieldNumber();
  public static final int kThreadIdFieldNumber = kThreadIdFieldNumber();
  public native @Cast("google::protobuf::uint32") int thread_id();
  public native void set_thread_id(@Cast("google::protobuf::uint32") int value);
}
