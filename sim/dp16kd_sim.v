// Behavioural model of the Lattice ECP5 DP16KD block RAM, for Verilator runs
// of the DP16KD build of solver.py (yosys ships only a black box).
//
// It covers what solver.py instantiates and checks the rest at time zero:
//   DATA_WIDTH_A == DATA_WIDTH_B in 1, 2, 4, 9, 18; REGMODE NOREG (1-cycle
//   read latency); CSDECODE 0b000 with CS pins low; RESETMODE SYNC; CLKA and
//   CLKB the same clock; WRITEMODE NORMAL, WRITETHROUGH or READBEFOREWRITE
//   (the data out of a port that writes: unchanged, new, old).
// Address pins (as yosys' ecp5/brams_map.v wires them): the word address is
// AD[13:k] with k = 0, 1, 2, 3, 4 for widths 1, 2, 4, 9, 18; for x18,
// ADx[1:0] are the byte enables of a write; other low pins are ignored. Data
// is on DI/DO[width-1:0]. The array is zero at time zero (all INITVAL 0).
//
// A read on one port of the word written in the same cycle on the other port
// is a collision. Its data is undefined on the device, so the model returns
// a poisoned value chosen by the plusarg +dp16kd_collide=N:
//   0 old data, 1 inverted old data (default), 2 new data, 3 random.
// Collisions are counted per block and reported by `final` (on stderr) when
// +dp16kd_report is given. Writes to one word from both ports in the same
// cycle stop the simulation.
module DP16KD(
  input DIA17, DIA16, DIA15, DIA14, DIA13, DIA12, DIA11, DIA10, DIA9, DIA8, DIA7, DIA6, DIA5, DIA4, DIA3, DIA2, DIA1, DIA0,
  input ADA13, ADA12, ADA11, ADA10, ADA9, ADA8, ADA7, ADA6, ADA5, ADA4, ADA3, ADA2, ADA1, ADA0,
  input CEA, OCEA, CLKA, WEA, RSTA,
  input CSA2, CSA1, CSA0,
  output DOA17, DOA16, DOA15, DOA14, DOA13, DOA12, DOA11, DOA10, DOA9, DOA8, DOA7, DOA6, DOA5, DOA4, DOA3, DOA2, DOA1, DOA0,

  input DIB17, DIB16, DIB15, DIB14, DIB13, DIB12, DIB11, DIB10, DIB9, DIB8, DIB7, DIB6, DIB5, DIB4, DIB3, DIB2, DIB1, DIB0,
  input ADB13, ADB12, ADB11, ADB10, ADB9, ADB8, ADB7, ADB6, ADB5, ADB4, ADB3, ADB2, ADB1, ADB0,
  input CEB, OCEB, CLKB, WEB, RSTB,
  input CSB2, CSB1, CSB0,
  output DOB17, DOB16, DOB15, DOB14, DOB13, DOB12, DOB11, DOB10, DOB9, DOB8, DOB7, DOB6, DOB5, DOB4, DOB3, DOB2, DOB1, DOB0
);
  parameter DATA_WIDTH_A = 18;
  parameter DATA_WIDTH_B = 18;
  parameter REGMODE_A = "NOREG";
  parameter REGMODE_B = "NOREG";
  parameter RESETMODE = "SYNC";
  parameter ASYNC_RESET_RELEASE = "SYNC";
  parameter CSDECODE_A = "0b000";
  parameter CSDECODE_B = "0b000";
  parameter WRITEMODE_A = "NORMAL";
  parameter WRITEMODE_B = "NORMAL";
  parameter GSR = "ENABLED";

  localparam W = DATA_WIDTH_A;
  localparam K = W == 1 ? 0 : W == 2 ? 1 : W == 4 ? 2 : W == 9 ? 3 : 4;
  localparam D = 16384 >> K;
  localparam [1:0] WMA = WRITEMODE_A == "WRITETHROUGH" ? 1 : WRITEMODE_A == "READBEFOREWRITE" ? 2 : 0;
  localparam [1:0] WMB = WRITEMODE_B == "WRITETHROUGH" ? 1 : WRITEMODE_B == "READBEFOREWRITE" ? 2 : 0;

  wire [17:0] dia = {DIA17, DIA16, DIA15, DIA14, DIA13, DIA12, DIA11, DIA10, DIA9, DIA8, DIA7, DIA6, DIA5, DIA4, DIA3, DIA2, DIA1, DIA0};
  wire [17:0] dib = {DIB17, DIB16, DIB15, DIB14, DIB13, DIB12, DIB11, DIB10, DIB9, DIB8, DIB7, DIB6, DIB5, DIB4, DIB3, DIB2, DIB1, DIB0};
  wire [13:0] ada = {ADA13, ADA12, ADA11, ADA10, ADA9, ADA8, ADA7, ADA6, ADA5, ADA4, ADA3, ADA2, ADA1, ADA0};
  wire [13:0] adb = {ADB13, ADB12, ADB11, ADB10, ADB9, ADB8, ADB7, ADB6, ADB5, ADB4, ADB3, ADB2, ADB1, ADB0};
  wire [13-K:0] wa = ada[13:K];
  wire [13-K:0] wb = adb[13:K];

  reg [W-1:0] mem [0:D-1];
  reg [W-1:0] doa, dob;
  wire [17:0] doa18 = 18'(doa);  // zero-extended
  wire [17:0] dob18 = 18'(dob);
  assign {DOA17, DOA16, DOA15, DOA14, DOA13, DOA12, DOA11, DOA10, DOA9, DOA8, DOA7, DOA6, DOA5, DOA4, DOA3, DOA2, DOA1, DOA0} = doa18;
  assign {DOB17, DOB16, DOB15, DOB14, DOB13, DOB12, DOB11, DOB10, DOB9, DOB8, DOB7, DOB6, DOB5, DOB4, DOB3, DOB2, DOB1, DOB0} = dob18;

  integer collide_mode;
  integer collisions;
  integer i;
  initial begin
    if (DATA_WIDTH_A != DATA_WIDTH_B || !(W == 1 || W == 2 || W == 4 || W == 9 || W == 18))
      $fatal(1, "DP16KD model: unsupported DATA_WIDTH %0d/%0d", DATA_WIDTH_A, DATA_WIDTH_B);
    if (REGMODE_A != "NOREG" || REGMODE_B != "NOREG" || RESETMODE != "SYNC"
        || CSDECODE_A != "0b000" || CSDECODE_B != "0b000")
      $fatal(1, "DP16KD model: unsupported REGMODE/RESETMODE/CSDECODE");
    for (i = 0; i < D; i = i + 1) mem[i] = 0;
    doa = 0;
    dob = 0;
    collisions = 0;
    if (!$value$plusargs("dp16kd_collide=%d", collide_mode)) collide_mode = 1;
  end

  // The word a port writes: x18 has byte enables on AD[1:0].
  function [W-1:0] merge(input [W-1:0] old, input [17:0] di, input [1:0] be);
    reg [17:0] o;
    begin
      if (W == 18) begin
        o = 18'(old);
        if (be[0]) o[8:0] = di[8:0];
        if (be[1]) o[17:9] = di[17:9];
        merge = o[W-1:0];
      end else
        merge = di[W-1:0];
    end
  endfunction

  function [W-1:0] poison(input [W-1:0] old, input [W-1:0] nw);
    begin
      case (collide_mode)
        0: poison = old;
        2: poison = nw;
        3: poison = $random;
        default: poison = ~old;
      endcase
    end
  endfunction

  wire cs_a = {CSA2, CSA1, CSA0} == 3'b000;
  wire cs_b = {CSB2, CSB1, CSB0} == 3'b000;
  wire en_a = CEA & cs_a;
  wire en_b = CEB & cs_b;
  wire wr_a = en_a & WEA;
  wire wr_b = en_b & WEB;
  wire [1:0] be_a = W == 18 ? ada[1:0] : 2'b11;
  wire [1:0] be_b = W == 18 ? adb[1:0] : 2'b11;

  reg [W-1:0] old_a, old_b, new_a, new_b;
  always @(posedge CLKA) begin
    if (CLKB !== CLKA) $fatal(1, "DP16KD model: CLKA and CLKB must be the same clock");
    old_a = mem[wa];
    old_b = mem[wb];
    new_a = merge(old_a, dia, be_a);
    new_b = merge(old_b, dib, be_b);
    if (wr_a & wr_b & (wa == wb)) $fatal(1, "DP16KD model: both ports write one word");
    // Port A.
    if (RSTA) doa <= 0;
    else if (en_a) begin
      if (!WEA) doa <= (wr_b & (wb == wa)) ? poison(old_a, new_b) : old_a;
      else if (WMA == 1) doa <= new_a;
      else if (WMA == 2) doa <= old_a;
    end
    // Port B.
    if (RSTB) dob <= 0;
    else if (en_b) begin
      if (!WEB) dob <= (wr_a & (wa == wb)) ? poison(old_b, new_a) : old_b;
      else if (WMB == 1) dob <= new_b;
      else if (WMB == 2) dob <= old_b;
    end
    if ((wr_a & en_b & !WEB & (wa == wb)) | (wr_b & en_a & !WEA & (wa == wb)))
      collisions = collisions + 1;
    if (wr_a) mem[wa] <= new_a;
    if (wr_b) mem[wb] <= new_b;
  end

  final if (collisions != 0 && $test$plusargs("dp16kd_report"))
    $fwrite(32'h80000002, "dp16kd_collisions %m %0d\n", collisions);
endmodule
