import YM.SU5.Assay.Marquee
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 360000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock
namespace Etch
open Analysis Heat

variable {K:Calibration}(w:ℤ)(σ:Cover)
variable {m:Side}{L:Loom (K.c m)}{Y:Mark (K.c m) →ℂ}{D:ℝ}(p:Metered K m L Y D)
local notation "H" F:max=> Y ((F:Family K) m)
local notation "R"=>runnel K w σ
local notation "N"=> (K.c m).val
local notation "ρ"=> ruler K.B
variable {f:Family K}{S:Finset Cover}(hw:0≤w)(e:InTest K true S false f)(u:House K w σ 0 S){A:ℝ}(c:pay f A)
local notation "P"=>Panel K w σ f
variable (r:ℕ) (gas:2*(ruler K.B*w*r)≤((K.c m).val:ℤ))
variable {F:Family K}{l h:Cover}{n:ℕ}
include hw e u c p gas

private lemma duplicate (z:P l h n F)(i:Axis)(t:l i≤h i)(v:h i-l i≤2*(r:ℤ)):
    ∃ G:Family K, P (pet l i (2*l i-h i)) h (n*2) G ∧ ‖H F‖^2≤ ‖H G‖ :=by
  have ht: (R i (h i))≤ R i (l i)+N:=by
    have hr:0≤ρ:=(ruler_gene _).le
    have ha:= mul_le_mul_of_nonneg_left v (mul_nonneg hr hw)
    unfold runnel; linarith only [gas,ha]
  obtain ⟨⟨T,hT,b⟩,_⟩:=z.receives K w σ hw e u c
  have h0:Satin.region T (K.c m)⊆band (K.c m) i (parting K w σ i (2*l i)) K.ℓ:=
    enters_arc K i (x:= R i (l i)) (fun x y=> ⟨(b i x y).1,le_trans (b i x y).2 ht⟩) (parting_edge K w σ i _).symm
  refine ⟨mirror K i (parting K w σ i (2*l i)) F * F,?_,p.twiceX i (2*(2*σ i+w*(2*l i))) ((hT.support m).mono h0)⟩
  have z':P (pet l i (l i)) (pet h i (h i)) n F:=by rw [petID,petID]; exact z
  have zs:=Panel.turn K w σ i (2*l i) z'
  rw [show 2*l i -l i=l i from by ring] at zs
  have z'':=Panel.glue K w σ i (by omega) t zs z'
  rw [petID] at z'' -- matching other update first?
  rw [mul_two]; exact z''

lemma redraw (z:P l h n F)(k:ℕ)(i:Axis)(t:l i≤h i)(v:2^k*(h i-l i)≤4*(r:ℤ)):
    ∃ l',∃ G:Family K, P l' h (n*2^k) G ∧
       (∀j,h j-l' j=(if j=i then 2^k else (1:ℤ))*(h j-l j)) ∧ ‖H F‖^(2^k:ℕ)≤ ‖H G‖ :=by
 induction k with
 | zero=>exact ⟨l,F,by simpa using z,by simp,by simp⟩
 | succ k ih=>
    have ht:2^k*(h i-l i)≤ 2*(r:ℤ):=by rw [pow_succ] at v; linarith only [v]
    obtain ⟨b,G,z,hb,d⟩:=ih (by linarith)
    have hc:=hb i; rw [if_pos rfl] at hc
    have hv: 0≤h i-b i:=by rw [hc]; exact mul_nonneg (by positivity) (by omega)
    obtain ⟨X,v',hh⟩:=duplicate w σ p hw e u c r gas z i (by omega) (by rw [hc]; exact ht)
    refine ⟨pet b i (2*b i-h i),X,by rw [pow_succ,←mul_assoc]; exact v',?_,?_⟩
    · intro j; by_cases a:j=i
      · subst j; rw [pet_i,if_pos rfl,pow_succ]; linarith only [hc]
      specialize hb j; rw [if_neg a] at hb; rw [pet_j b a,if_neg a]; exact hb
    rw [pow_succ,pow_mul]; exact (pow_le_pow_left₀ (by positivity) d 2).trans hh -- which succ? rw first see

lemma rolls (z:P l h n F)(k:ℕ)(s:Finset Axis)(t:∀i,l i≤h i)(v:∀i∈s,2^k*(h i-l i)≤4*(r:ℤ)):
    ∃ l',∃ G:Family K, P l' h (n*(2^k)^s.card) G ∧
       (∀j,h j-l' j=(if j∈s then 2^k else (1:ℤ))*(h j-l j)) ∧ ‖H F‖^((2^k)^s.card:ℕ)≤ ‖H G‖ :=by
 induction s using Finset.induction_on with
 | empty=>exact ⟨l,F,by simpa using z,by simp,by simp⟩
 | @insert i s hx ih=>
    obtain ⟨b,G,z,hb,d⟩:=ih (fun j g=> v j (mem_insert_of_mem g))
    have hc:=hb i; rw [if_neg hx,one_mul] at hc
    have t':b i≤h i:=by specialize t i; omega
    have v':2^k*(h i-b i)≤4*(r:ℤ):= by rw [hc]; exact v i (mem_insert_self i _)
    obtain ⟨a,F',z',ha,e'⟩:=redraw w σ p hw e u c r gas z k i t' v'
    rw [card_insert_of_notMem hx,pow_succ] -- pow_succ Nat or Real? same exp count
    refine ⟨a,F',by rw [←mul_assoc]; exact z',?_,?_⟩
    · intro j; by_cases g:j=i
      · subst j; rw [ha i,if_pos rfl,hc,if_pos (mem_insert_self i _)]
      rw [ha,if_neg g,one_mul,hb]; simp only [mem_insert,or_iff_right g]
    rw [pow_mul]; exact (pow_le_pow_left₀ (by positivity) d _).trans e'

omit p hw e u c gas

def Full (r n:ℕ):Prop:=(4*r)^4≤8*n∧ n≤(4*r)^4
def Hall (r:ℕ)(l h:Cover):Prop:=∀i,l i≤h i∧h i-l i≤4*(r:ℤ)
def Mosaic (w:ℤ)(σ:Cover)(r:ℕ)(f:Family K)(q:ℝ)(Z:Family K→ℂ):Prop:=
 ∀ (l h:Cover)(n:ℕ), Full r n → Hall r l h → ∀ F:Family K, Panel K w σ f l h n F → ‖Z F‖≤q^n

private lemma scales(x b:ℕ)(pb:0< b)(h: b≤x): ∃ k:ℕ,2^k*b ≤ x ∧ x ≤2*2^k*b:=by
 have e:x ≤ 2^x*b := (Nat.lt_two_pow_self.le).trans (Nat.le_mul_of_pos_right _ pb)
 let Gq(k:ℕ):=x ≤2*2^k*b
 have t:∃ k,Gq k:= ⟨x,by unfold Gq; linarith⟩
 refine ⟨Nat.find t,?_,Nat.find_spec t⟩
 generalize hx:Nat.find t=y
 cases y with
 | zero=> exact (one_mul b).symm ▸ h
 | succ j=>
    have u:= Nat.find_min t (m:=j) (by omega)
    rw [pow_succ']; unfold Gq at u; exact (not_le.mp u).le

include p hw e u c gas
lemma bannerView (j:Axis)(he:σ j=0)(hr:0<r)(q:ℝ)(hq:0≤q) (y:Mosaic w σ r f q (fun x=> Y (x m))) (a:ℤ):
 ‖H (banner j w (w*a) r f)‖ ≤ q^(4*r):=by
 let F₀ := banner j w (w*a) r f; let l₀:=pet 0 j (a-3*r); let h₀:=pet 1 j (a+r)
 have z:P l₀ h₀ (4*r) F₀:=marquee K w σ j f he r a
 have ht(i:Axis): h₀ i-l₀ i= if i=j then 4*(r:ℤ) else 1:=by
    unfold h₀ l₀
    by_cases g:i=j
    · subst i; rw [if_pos rfl,pet_i,pet_i]; ring
    rw [pet_j _ g,pet_j _ g,if_neg g,Pi.one_apply,Pi.zero_apply,sub_zero]
 have h'i(i:Axis):l₀ i≤h₀ i:=by have g:=ht i; split_ifs at g <;> omega
 let s:=univ.erase j
 have h₁:s.card=3:=by rw [show s=_ from rflX j,card_erase_of_mem (mem_univ _),card_univ,show Fintype.card Axis=4 from Fintype.card_fin 4]
 obtain ⟨k,hk,hv⟩:=scales (4*r) 1 (by omega) (by omega); rw [mul_one] at hk hv
 have hx(i:Axis)(a:i∈s):2^k*(h₀ i-l₀ i)≤4*(r:ℤ):=by
   rw [ht i,if_neg (mem_erase.mp a).1,mul_one]; exact_mod_cast hk
 obtain ⟨b,G,t,e,d⟩:=rolls w σ p hw e u c r gas z k s h'i hx
 have hh:Hall r b h₀:=by
    intro i
    have hg:=e i; rw [ht i] at hg
    by_cases g:i=j
    · subst i; unfold s at hg; rw [if_pos rfl,if_neg (notMem_erase _ _),one_mul] at hg; omega
    rw [if_neg g,if_pos (mem_erase.mpr ⟨g,mem_univ _⟩),mul_one] at hg
    have hj:(2:ℤ)^k≤4*(r:ℤ):=by exact_mod_cast hk
    have ht':0≤(2:ℤ)^k:=by positivity
    omega
 let J:=(2^k)^s.card; have hJ:0<(J:ℕ):=by unfold J; positivity
 have hf:Full r (4*r*J):=by
    unfold J; rw [h₁]; constructor
    · calc
       _=4*r*(4*r)^3:=by ring
       _≤4*r*(2*2^k)^3:=by gcongr
       _=_:=by ring
    rw [show (4*r)^4=4*r*(4*r)^3 from by ring]; gcongr
 apply (pow_le_pow_iff_left₀ (norm_nonneg _) (pow_nonneg hq _) (n:=J) (by omega)).mp
 rw [←pow_mul]
 exact d.trans (y b h₀ _ hf hh G t)
where rflX (j:Axis): univ.erase j=(univ.erase j):=rfl

end Etch
end YM.CF.Buffered.Afterglow.Tower.SlabMark
