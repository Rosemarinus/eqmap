// RUN: eqmap_fpga %s --disassemble NOR,INV,AND -s 140000 2>>/dev/null | FileCheck %s

module mux_4_1 (
    b,
    a,
    d,
    c,
    s0,
    s1,
    y
);
  input b;
  wire b;
  input a;
  wire a;
  input d;
  wire d;
  input c;
  wire c;
  input s0;
  wire s0;
  input s1;
  wire s1;
  output y;
  wire y;
  wire tmp7;
  LUT4 #(
      .INIT(16'hf0ca)
  ) __0__ (
      .I0(d),
      .I1(c),
      .I2(s0),
      .I3(s1),
      .O (tmp7)
  );
  LUT4 #(
      .INIT(16'hcaf0)
  ) __1__ (
      .I0(b),
      .I1(a),
      .I2(tmp7),
      .I3(s1),
      .O (y)
  );

  // CHECK: NOT #(
  // CHECK: ) __12__ (
  // CHECK:     .A(s0),
  // CHECK:     .Y(__0__)
  // CHECK: );
  // CHECK: AND #(
  // CHECK: ) __13__ (
  // CHECK:     .A(b),
  // CHECK:     .B(__0__),
  // CHECK:     .Y(__1__)
  // CHECK: );
  // CHECK: AND #(
  // CHECK: ) __14__ (
  // CHECK:     .A(a),
  // CHECK:     .B(s0),
  // CHECK:     .Y(__2__)
  // CHECK: );
  // CHECK: NOR #(
  // CHECK: ) __15__ (
  // CHECK:     .A(__2__),
  // CHECK:     .B(__1__),
  // CHECK:     .Y(__3__)
  // CHECK: );
  // CHECK: NOT #(
  // CHECK: ) __16__ (
  // CHECK:     .A(s1),
  // CHECK:     .Y(__4__)
  // CHECK: );
  // CHECK: NOR #(
  // CHECK: ) __17__ (
  // CHECK:     .A(__4__),
  // CHECK:     .B(__3__),
  // CHECK:     .Y(__5__)
  // CHECK: );
  // CHECK: AND #(
  // CHECK: ) __18__ (
  // CHECK:     .A(c),
  // CHECK:     .B(s0),
  // CHECK:     .Y(__6__)
  // CHECK: );
  // CHECK: NOT #(
  // CHECK: ) __19__ (
  // CHECK:     .A(d),
  // CHECK:     .Y(__7__)
  // CHECK: );
  // CHECK: NOR #(
  // CHECK: ) __20__ (
  // CHECK:     .A(s0),
  // CHECK:     .B(__7__),
  // CHECK:     .Y(__8__)
  // CHECK: );
  // CHECK: NOR #(
  // CHECK: ) __21__ (
  // CHECK:     .A(__8__),
  // CHECK:     .B(__6__),
  // CHECK:     .Y(__9__)
  // CHECK: );
  // CHECK: NOR #(
  // CHECK: ) __22__ (
  // CHECK:     .A(s1),
  // CHECK:     .B(__9__),
  // CHECK:     .Y(__10__)
  // CHECK: );
  // CHECK: NOR #(
  // CHECK: ) __23__ (
  // CHECK:     .A(__10__),
  // CHECK:     .B(__5__),
  // CHECK:     .Y(__11__)
  // CHECK: );
  // CHECK: NOT #(
  // CHECK: ) __24__ (
  // CHECK:     .A(__11__),
  // CHECK:     .Y(y)
  // CHECK: );

  // NOT #(
  // ) __12__ (
  //     .A(s0),
  //     .Y(__0__)
  // );
  // AND #(
  // ) __13__ (
  //     .A(b),
  //     .B(__0__),
  //     .Y(__1__)
  // );
  // AND #(
  // ) __14__ (
  //     .A(a),
  //     .B(s0),
  //     .Y(__2__)
  // );
  // NOR #(
  // ) __15__ (
  //     .A(__2__),
  //     .B(__1__),
  //     .Y(__3__)
  // );
  // NOT #(
  // ) __16__ (
  //     .A(__3__),
  //     .Y(__4__)
  // );
  // AND #(
  // ) __17__ (
  //     .A(s1),
  //     .B(__4__),
  //     .Y(__5__)
  // );
  // NOT #(
  // ) __18__ (
  //     .A(d),
  //     .Y(__6__)
  // );
  // NOR #(
  // ) __19__ (
  //     .A(s0),
  //     .B(__6__),
  //     .Y(__7__)
  // );
  // AND #(
  // ) __20__ (
  //     .A(c),
  //     .B(s0),
  //     .Y(__8__)
  // );
  // NOR #(
  // ) __21__ (
  //     .A(__8__),
  //     .B(__7__),
  //     .Y(__9__)
  // );
  // NOR #(
  // ) __22__ (
  //     .A(s1),
  //     .B(__9__),
  //     .Y(__10__)
  // );
  // NOR #(
  // ) __23__ (
  //     .A(__10__),
  //     .B(__5__),
  //     .Y(__11__)
  // );
  // NOT #(
  // ) __24__ (
  //     .A(__11__),
  //     .Y(y)
  // );

endmodule
