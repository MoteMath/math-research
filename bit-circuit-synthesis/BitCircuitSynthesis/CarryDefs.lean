import BitCircuitSynthesis.BigBangScratchVerify
import BitCircuitSynthesis.Epoch7PrimesVerify
import BitCircuitSynthesis.Epoch10AllThreeVerify
import BitCircuitSynthesis.Stage3CarryRHVerify
import BitCircuitSynthesis.Waves13To16Verify

namespace SiliconBigBang

def bpos_deg : BPos → BBin
  | BPos.one  => BBin.zero
  | BPos.x0 p => bsucc (bpos_deg p)
  | BPos.x1 p => bsucc (bpos_deg p)

def bp_three : BPos := BPos.x1 BPos.one

def bp_five  : BPos := BPos.x1 (BPos.x0 BPos.one)

def bp_nine  : BPos := BPos.x1 (BPos.x0 (BPos.x0 BPos.one))

def bartin_schreier_op (x : BBin) : BBin :=
  bxor_bin (bfrob2 x) x

def bfrob_pow : BUnary → BBin → BBin
  | BUnary.uz,   x => x
  | BUnary.us u, x => bfrob2 (bfrob_pow u x)

def bfrob_trace : BUnary → BBin → BBin
  | BUnary.uz,   _ => BBin.zero
  | BUnary.us u, x => bxor_bin x (bfrob2 (bfrob_trace u x))

end SiliconBigBang
