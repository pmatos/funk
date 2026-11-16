module @dev() {
  dialects gpu

  func @item() -> i32, i32, i32 {
  ^e:
    %x: i32 = gpu.work_item_id gpu.x @0
    %y: i32 = gpu.work_item_id gpu.y @0
    %z: i32 = gpu.work_item_id gpu.z @0
    ret %x, %y, %z @0
  }

  func @group() -> i32, i32, i32 {
  ^e:
    %x: i32 = gpu.work_group_id gpu.x @0
    %y: i32 = gpu.work_group_id gpu.y @0
    %z: i32 = gpu.work_group_id gpu.z @0
    ret %x, %y, %z @0
  }

  func @size() -> i32, i32, i32 {
  ^e:
    %x: i32 = gpu.work_group_size gpu.x @0
    %y: i32 = gpu.work_group_size gpu.y @0
    %z: i32 = gpu.work_group_size gpu.z @0
    ret %x, %y, %z @0
  }

  func @groups() -> i32, i32, i32 {
  ^e:
    %x: i32 = gpu.num_work_groups gpu.x @0
    %y: i32 = gpu.num_work_groups gpu.y @0
    %z: i32 = gpu.num_work_groups gpu.z @0
    ret %x, %y, %z @0
  }

}

locs {
  @0 = unknown
}
