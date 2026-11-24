import ZecaThresh
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

/-- ferret copies on exact pitch inside an open interval -/
structure Skiff5 where
 k:ℕ
 num:ℤ
deriving DecidableEq
def Skiff5.d (y:Skiff5):ℝ:= y.num/5^y.k
def push5 (r:ℝ)(k:ℕ):Skiff5:=⟨k,⌊r*(5:ℝ)^k⌋+1⟩
lemma push5_cap (r:ℝ)(k:ℕ): r < (push5 r k).d ∧ (push5 r k).d ≤ r+ 1/(5:ℝ)^k:=by
 have e:=Int.lt_floor_add_one (r*(5:ℝ)^k)
 have d:=Int.floor_le (r*(5:ℝ)^k)
 unfold push5 Skiff5.d
 have p:0<(5:ℝ)^k:=by positivity
 rw [Int.cast_add,Int.cast_one]
 refine ⟨(lt_div_iff₀ p).mpr e, (div_le_iff₀ p).mpr ?_⟩
 rw [add_mul,div_mul_cancel₀ _ p.ne'];gcongr
lemma push5_go(r:ℝ):Tendsto (Skiff5.d ∘ push5 r) atTop (𝓝 r):=by
 apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _
        (fun k=>(push5_cap r k).1.le) (fun k=>(push5_cap r k).2)
 have h:Tendsto (fun k:ℕ=>1/(5:ℝ)^k) atTop (𝓝 0):=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
 simpa only [add_zero] using h.const_add r

def brig(a b:ℝ):={i:Skiff5 // i.d∈Set.Ioo a b}
abbrev beam5(a b:ℝ) : brig a b → ℝ:= fun j=>j.val.d
lemma cask_in {b r:ℝ}(v:r∈Set.Icc 0 b):(r:ℂ)∈cask (b+1):=by
 refine ⟨?_, by rw [Complex.ofReal_im,abs_zero];norm_num⟩
 rw [Complex.norm_real,Real.norm_of_nonneg v.1]
 exact v.2.trans_lt (lt_add_one _)
lemma hull5 {a b:ℝ} (h:0≤a) (p:a<b):
 Weather (cask (b+1)) (beam5 a b):=by
 let d:=beam5 a b
 have w:0<b:=h.trans_lt p
 obtain ⟨r,ra,rb⟩:=exists_between p
 refine ⟨cask_open _,fun i=>cask_in ⟨h.trans i.2.1.le,i.2.2.le⟩,
   Set.Icc 0 b,isPreconnected_Icc,fun _=>cask_in,⟨le_rfl,w.le⟩,r,⟨h.trans ra.le,rb.le⟩,?_⟩
 have q:Tendsto (Skiff5.d ∘ push5 r) atTop (𝓝[≠] r):= tendsto_nhdsWithin_iff.mpr
   ⟨push5_go r, Eventually.of_forall fun n=> (push5_cap r n).1.ne'⟩
 exact q.frequently (show ∃ᶠ k:ℕ in atTop, _ from
     ((push5_go r).eventually (Ioo_mem_nhds ra rb)).frequently.mono
       (fun k u=> ⟨⟨push5 r k,u⟩,rfl⟩)) -- tune
#print axioms hull5
