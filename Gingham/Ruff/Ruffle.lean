import YM.CF.Sault.Gilt

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]



/-! Algebraic data for (125)-(128) of XXI. S is spar, T = Aim.den,
A is tickA. W an arbitrary one-body weight (for the divergence source it
will be the Hermitian projection onto a full block).  We isolate the unit
triangular change C and its polynomial inverse. -/

abbrev ℱ (S T : Op n) := Kennel.capT S T
def 𝒞 (S T : Op n) : Op n := 1 + ℱ S T
def 𝒞' (S T : Op n) : Op n := 1 - ℱ S T
def seam (S W : Op n) : Op n := S*W*S + (1-S)*W*(1-S)
def sheaf (S T W : Op n) := 𝒞 S T * seam S W * 𝒞' S T
def 𝒪 (S T W : Op n) := W - sheaf S T W
def 𝒜 (S A W : Op n) := Matrix.trace ((S-A)*W)

/-- The reduced form of (125). -/
def 𝒵 (S T W : Op n) : FC n := Matrix.trace (S*W) • 1 - dg (sheaf S T W)
/-- The last parentheses in (125). -/
def gable (A W : Op n) : FC n := dg W - Matrix.trace (A * W) • 1
/-- The expression before normal/dark price. -/
def facade (A W : Op n) (a : ℂ) (O : Op n) := a • (1:FC n) + dg O - gable A W

lemma dg_sub (X Y : Op n) : dg (X-Y) = dg X - dg Y := by
  rw [sub_eq_add_neg,dg_add,dg_neg,sub_eq_add_neg]
lemma dg_zero : dg (0:Op n)=0 := by simp [dg,dyad]


lemma facade_eq (S T W A : Op n) :
    facade A W (𝒜 S A W) (𝒪 S T W) = 𝒵 S T W := by
  rw [facade,𝒜,sub_mul,Matrix.trace_sub,sub_smul,gable,𝒪,dg_sub,𝒵]
  abel

variable {S : Op n}

lemma P'orth (h : IsStarProjection S) : (1-S)*S = 0 := by
  rw [sub_mul,one_mul,h.isIdempotentElem.eq,sub_self]

lemma ℱ_nil (h : IsStarProjection S) (T : Op n) : ℱ S T * ℱ S T = 0 := by
  unfold ℱ Kennel.capT
  -- left assoc.
  rw [mul_assoc _ S,←mul_assoc S,←mul_assoc S,Porth h,zero_mul,zero_mul,mul_zero]

lemma 𝒞'inv (h : IsStarProjection S) (T : Op n) :
    𝒞' S T * 𝒞 S T = 1 := by
  rw [𝒞',𝒞,mul_add,sub_mul,sub_mul,mul_one,mul_one,one_mul,ℱ_nil h]
  abel
lemma 𝒞inv (h : IsStarProjection S) (T : Op n) :
    𝒞 S T * 𝒞' S T = 1 := mul_eq_one_comm.mp (𝒞'inv h T)
lemma 𝒞_quant (h : IsStarProjection S) (T : Op n) :
    quant (𝒞 S T) = exp (dg (ℱ S T)) := (tallied _ (ℱ_nil h T)).symm


lemma seam_s (h : IsStarProjection S) (W : Op n) : S * seam S W = S*W*S := by
  rw [seam,mul_add,←mul_assoc S,←mul_assoc S,h.isIdempotentElem.eq,
    ←mul_assoc S ( (1-S)*W),←mul_assoc S (1-S),Porth h,zero_mul,zero_mul,add_zero]
lemma seam_comm (h : IsStarProjection S) (W : Op n) : Commute S (seam S W) := by
  change S * seam S W = seam S W * S
  rw [seam_s h,seam,add_mul,mul_assoc (S*W), h.isIdempotentElem.eq,
    mul_assoc ((1-S)*W),P'orth h,mul_zero,add_zero]
lemma seam_trace (h : IsStarProjection S) (W : Op n) :
    Matrix.trace (S*seam S W) = Matrix.trace (S*W) := by
  rw [seam_s h, Matrix.trace_mul_comm, ←mul_assoc,h.isIdempotentElem.eq]
lemma seam_full_trace (h : IsStarProjection S) (W : Op n) :
    Matrix.trace (seam S W) = Matrix.trace W := by
  rw [seam,Matrix.trace_add,Matrix.trace_mul_comm,Matrix.trace_mul_comm ((1-S)*W),
    ←mul_assoc,h.isIdempotentElem.eq,←mul_assoc (1-S),
    h.one_sub.isIdempotentElem.eq,sub_mul,one_mul,Matrix.trace_sub]
  abel

lemma sheaf_trace (h : IsStarProjection S) (T W : Op n) :
    Matrix.trace (sheaf S T W) = Matrix.trace W := by
  rw [sheaf,Matrix.trace_mul_comm,←mul_assoc,𝒞'inv h,one_mul,seam_full_trace h]
lemma 𝒪_trace (h : IsStarProjection S) (T W : Op n) :
    Matrix.trace (𝒪 S T W) = 0 := by
  rw [𝒪, Matrix.trace_sub,sheaf_trace h,sub_self]


lemma sheaf_p (h : IsStarProjection S) (T W : Op n) :
    S * sheaf S T W = S * W * S := by
  have r : S * ℱ S T = 0 := by
    unfold ℱ Kennel.capT; rw [←mul_assoc,←mul_assoc,Porth h,zero_mul,zero_mul]
  rw [sheaf,𝒞,𝒞',←mul_assoc,←mul_assoc,mul_add S,mul_one,r,add_zero,seam_s h,
    mul_sub,mul_one,mul_assoc (S*W),r,mul_zero,sub_zero]

lemma sheaf_q (h : IsStarProjection S) (T W : Op n) :
    sheaf S T W * (1-S) = (1-S) * W * (1-S) := by
  have r : ℱ S T * (1-S) = 0 := by
    unfold ℱ Kennel.capT; rw [mul_assoc,Porth h,mul_zero]
  have u : seam S W * (1-S) = (1-S)*W*(1-S) := by
    rw [seam,add_mul,mul_assoc (S*W),Porth h,mul_zero,zero_add,
      mul_assoc,h.one_sub.isIdempotentElem.eq]
  rw [sheaf,𝒞,𝒞',mul_assoc,sub_mul,one_mul,r,sub_zero,mul_assoc,u,
    add_mul,one_mul,←mul_assoc (ℱ S T),←mul_assoc (ℱ S T),r,zero_mul,zero_mul,add_zero]

lemma 𝒪_one (h : IsStarProjection S) (T : Op n) :
    𝒪 S T 1 = 0 := by
  have u : seam S 1 = 1 := by
    rw [seam,mul_one,mul_one,h.isIdempotentElem.eq,h.one_sub.isIdempotentElem.eq]
    abel
  rw [𝒪,sheaf,u,mul_one,𝒞inv h,sub_self]


lemma 𝒪_sum {ι : Type*} (i : Finset ι) (W : ι → Op n) (S T : Op n) :
    ∑ a ∈ i, 𝒪 S T (W a) = 𝒪 S T (∑ a ∈ i, W a) := by
  simp only [𝒪,sheaf,seam,sum_sub_distrib,mul_sum,sum_mul,sum_add_distrib,
    add_mul,mul_add]
lemma 𝒪_partition {ι : Type*} {i : Finset ι} {W : ι → Op n}
    (h : IsStarProjection S) (g : ∑ a ∈ i, W a = 1) (T : Op n) :
    ∑ a ∈ i, 𝒪 S T (W a) = 0 := by rw [𝒪_sum,g,𝒪_one h]

/-- Exact cancellation on comparator, all T. -/
theorem voiceless (h : IsStarProjection S) (q : Wave n) (u : Sea S q) (T W : Op n) :
    acts (𝒵 S T W) (acts (quant (𝒞 S T)) q) = 0 := by
  have he := Sault.loft_v _ (seam_comm h W) h q u
  rw [seam_trace h] at he
  have uw : 𝒞' S T * sheaf S T W * 𝒞 S T = seam S W := by
    rw [sheaf,←mul_assoc,←mul_assoc,𝒞'inv h, one_mul,mul_assoc,𝒞'inv h,mul_one]
  rw [𝒵,act_sub,act_smul,act_one,←act_mul _ (quant _),
    Sault.zeal _ _ (𝒞'inv h _),uw,act_mul,he,map_smul,sub_self]

