// RUN: eqmap_fpga %s --assert-sat -k 4 | FileCheck %s

module mux_4_1 (
    a,
    b,
    c,
    d,
    s0,
    s1,
    y
);
  input a;
  wire a;
  input b;
  wire b;
  input c;
  wire c;
  input d;
  wire d;
  input s0;
  wire s0;
  input s1;
  wire s1;
  output y;
  wire y;
  LUT6 #(
      .INIT(64'd17361601744336890538)
  ) _0_ (
      .I0(d),
      .I1(c),
      .I2(a),
      .I3(b),
      .I4(s1),
      .I5(s0),
      .O (y)
  );
endmodule

// CHECK: module mux_4_1 (
// CHECK:     b,
// CHECK:     a,
// CHECK:     d,
// CHECK:     c,
// CHECK:     s0,
// CHECK:     s1,
// CHECK:     y
// CHECK: );
// CHECK:   input b;
// CHECK:   wire b;
// CHECK:   input a;
// CHECK:   wire a;
// CHECK:   input d;
// CHECK:   wire d;
// CHECK:   input c;
// CHECK:   wire c;
// CHECK:   input s0;
// CHECK:   wire s0;
// CHECK:   input s1;
// CHECK:   wire s1;
// CHECK:   output y;
// CHECK:   wire y;
// CHECK:   wire __0__;
// CHECK:   LUT4 #(
// CHECK:       .INIT(16'hf0ca)
// CHECK:   ) __1__ (
// CHECK:       .I0(d),
// CHECK:       .I1(c),
// CHECK:       .I2(s0),
// CHECK:       .I3(s1),
// CHECK:       .O(__0__)
// CHECK:   );
// CHECK:   LUT4 #(
// CHECK:       .INIT(16'hcaf0)
// CHECK:   ) __2__ (
// CHECK:       .I0(b),
// CHECK:       .I1(a),
// CHECK:       .I2(__0__),
// CHECK:       .I3(s1),
// CHECK:       .O(y)
// CHECK:   );
// CHECK: endmodule

//  module mux_4_1 (
//      c,
//      a,
//      d,
//      b,
//      s1,
//      s0,
//      y
//  );
//    input c;
//    wire c;
//    input a;
//    wire a;
//    input d;
//    wire d;
//    input b;
//    wire b;
//    input s1;
//    wire s1;
//    input s0;
//    wire s0;
//    output y;
//    wire y;
//    wire __0__;
//    LUT4 #(
//        .INIT(16'hf0ca)
//    ) __1__ (
//        .I0(d),
//        .I1(b),
//        .I2(s1),
//        .I3(s0),
//        .O(__0__)
//    );
//    LUT4 #(
//        .INIT(16'hcaf0)
//    ) __2__ (
//        .I0(c),
//        .I1(a),
//        .I2(__0__),
//        .I3(s0),
//        .O(y)
//    );
//  endmodule
