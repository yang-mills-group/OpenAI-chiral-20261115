import YM.SU5.Relativistic.Darner
import YM.SU5.Relativistic.Pageant
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.Mosaic
open Function Finset Filter MeasureTheory Lattice Wilson Fixed.Pivots GaugeFlux
open scoped Matrix BigOperators
variable {N C: Side}(L:Ratio C N)
local notation "W_"=> L.count
local notation "T_"=> Site C
local notation "F_"=> Site N
local notation "P_"=> Site L.count
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
open RG RG.PathData Work.F03 Pharos
open MinorPins Precision Exterior Pageant Matrix
variable {V:Side}
section algebra
variable {I J: Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
theorem grit (v:I→ℝ): dotProduct v v=∑ i, v i^2:= by simp only [dotProduct,sq]
lemma grant_sq (e:I ↪ J)(v:I→ℝ): dotProduct (smear e *ᵥ v) (smear e *ᵥ v)=dotProduct v v:=by
 let F:= smear e *ᵥ v; rw [grit,grit]; change (∑ i,F i^2)=_; rw [←sum_subset (s₁:=(univ:Finset I).image e) (subset_univ _)]; · rw [sum_image (by intro i _ j _ h; exact e.injective h)]; simp only [F,smear_t]
 intro i p t; rw [show F i=0 from smear_f _ _ (by simpa [Set.mem_range] using t)]; norm_num
lemma pts {G:Gauge} (v:G.Color) : ‖v‖^2=∑ i,v i^2:= EuclideanSpace.real_norm_sq_eq v -- tune
end algebra
variable (G:Gauge)
-- Gram matrix for ort tile. Want dimensions for volume chart as product live × color
abbrev Lo (V:Side):= ↥(livelies V)
abbrev Fresco (V:Side) := Lo V × G.ColorIndex
def crosses (V:Side) : Fresco G V ↪ Ink G V := Embedding.prodMap (Embedding.subtype _) (Embedding.refl _)
local notation "E_"=> Fresco G V
local notation "Ι"=> Ink G V
local notation "Ξ"=> Face (Per V)
def drafts {I : Type}[Fintype I][DecidableEq I]{U:Side}(e:I ↪ Ink G U)(v:I→ℝ) := laced G (smear e *ᵥ v)
abbrev brightQ (V:Side):= drafts G (crosses G V)
-- linear estate
def curlLin (i: Face (Per N)):(Ink G N→ℝ)→ₗ[ℝ] G.Color where
 toFun f := faceCurl i (laced G f)
 map_add' f g:=by
    ext j; simp only [PiLp.add_apply,atCurl]; unfold Curl; simp only [Pi.add_apply]; ring
 map_smul' t f:=by
    ext j; simp only [PiLp.smul_apply,RingHom.id_apply,atCurl]; unfold Curl; simp only [Pi.smul_apply,smul_eq_mul]; ring
local notation "li"=> curlLin G
variable (W:PathData G)(D:ℕ)
def trig (u:Ink G N→ℝ)(p:Face (Per N))(i:ℕ):G.Color:= let Z:=W.row p.2 i; if Z.2.length≤D then Z.1 • li (slotFace Z.2 p.1) u else 0
def cropL (u:fieldDir G V 1)(i:Face (Per V)):= cutlow W (curling u) i D -- include G? namespace
variable {p:Clip}{σ Cc Λ:ℝ} (B:W.Bounds p σ Cc Λ)
lemma crop_sing(f:Ink G N→ℝ)(i:Face (Per N)) : (∑' j,trig G W D f i j)= cropL G W D (laced G f) i:=rfl
include B in
lemma summT (u:Ink G V→ℝ)(i :Face (Per V)) : Summable (trig G W D u i):=by
 have he:= ellLine_summable W B i (laced G u);
 apply Summable.of_norm_bounded he.norm
 intro n; unfold trig; dsimp only; split; · rfl
 rw [norm_zero]; exact norm_nonneg _
private def phire (i:Face (Per V)) : (Ink G V→ℝ)→ₗ[ℝ]G.Color where
 toFun t:= cropL G W D (laced G t) i
 map_add' f g:=by
    rw [←crop_sing,←crop_sing,←crop_sing, ← (summT G W D B f i).tsum_add (summT G W D B g i)]
    apply tsum_congr; intro j; unfold trig; dsimp only; split; · rw [map_add,smul_add]
    rw [add_zero]
 map_smul' α f:=by
    rw [←crop_sing,←crop_sing,RingHom.id_apply,← tsum_const_smul'']; apply tsum_congr; intro j; unfold trig; dsimp only; split; · rw [map_smul,smul_comm]
    rw [smul_zero]

-- independence proofs B later
private def blockM {I:Type}[Fintype I][DecidableEq I](b: (E_→ℝ)→ₗ[ℝ](I→ℝ)):Matrix (E_) (E_) ℝ := let t:= LinearMap.toMatrix' b; t.transpose*t
private def directMap (V:Side): (Fresco G V→ℝ)→ₗ[ℝ]((↥(ort V)×G.ColorIndex)→ℝ):= LinearMap.pi fun x=> (PiLp.projₗ 2 _ x.2).comp ((li x.1.val).comp (smear (crosses G V)).mulVecLin)
private def lMap (V:Side): (Fresco G V→ℝ)→ₗ[ℝ]((↥(plumb V D)×G.ColorIndex)→ℝ):= LinearMap.pi fun x=>(PiLp.projₗ 2 _ x.2).comp ((phire G W D B x.1.val).comp (smear (crosses G V)).mulVecLin)
def DueQ (V:Side):= p.direct • blockM G (directMap G V)+ blockM G (lMap G W D B V)
private lemma sq_block {I:Type}[Fintype I][DecidableEq I](b:(E_→ℝ)→ₗ[ℝ](I→ℝ))(v:E_→ℝ): dotProduct v ((blockM G b)*ᵥ v)=∑ i,(b v i)^2:=by unfold blockM; dsimp only; rw [←mulVec_mulVec,dotProduct_transpose_mulVec,LinearMap.toMatrix'_mulVec,grit]
abbrev shortV (u:fieldDir G V 1):= ∑ i ∈ plumb V D,‖cropL G W D u i‖^2
def inCurl (u:fieldDir G V 1):=∑ i∈ort V, ‖faceCurl i u‖^2
lemma ledgerQ(v:E_→ℝ): let u:=brightQ G V v; dotProduct v (DueQ G W D B V *ᵥ v)= p.direct*inCurl G u + shortV G W D u:=by
 intro u; rw [DueQ,Matrix.add_mulVec,dotProduct_add,Matrix.smul_mulVec,dotProduct_smul,sq_block,sq_block,Fintype.sum_prod_type,Fintype.sum_prod_type]; unfold inCurl shortV; simp_rw [pts]; rw [← sum_attach (ort V),←sum_attach (plumb V D)] <;> try rfl
lemma clearQ (V:Side):(DueQ G W D B V).transpose= DueQ G W D B V:=by unfold DueQ blockM; simp only [transpose_add,transpose_smul,transpose_mul,transpose_transpose]

def hatp (G:Gauge)(V:Side):ℝ:=1+(4*V.val^4*(Fintype.card G.ColorIndex):ℝ)*((limit V:ℕ):ℝ)^2
theorem count_f (V:Side) : (Fintype.card (Fresco G V):ℝ) ≤ 4*(V.val:ℝ)^4*Fintype.card G.ColorIndex:=by
 have he:Fintype.card (Fresco G V) ≤ 4*V.val^4*Fintype.card G.ColorIndex:=by unfold Fresco Lo; rw [Fintype.card_prod,Fintype.card_coe]; refine Nat.mul_le_mul_right _ ((card_le_univ _).trans_eq ?_); unfold Link Edge; rw [Fintype.card_prod,Lattice.site_card,show Fintype.card Axis=4 from rfl,Nat.mul_comm]
 exact_mod_cast he
lemma shrine (v:E_→ℝ): dotProduct v v ≤ hatp G V * inCurl G (brightQ G V v):=by
 let e:= crosses G V; let u:=brightQ G V v; let Z:= Real.sqrt (inCurl G u); have he:0≤ inCurl G u:=sum_nonneg fun _ _=>sq_nonneg _; have hx:= Real.sqrt_nonneg (inCurl G u)
 have hp(a:Link V)(i:G.ColorIndex)(t:indoors a)(q:¬Active a): (smear e*ᵥ v) (a,i)=0:= smear_f _ _ (by rintro ⟨y,p⟩; rcases y with ⟨⟨x,h⟩,j⟩; exact q ((show x=a from congrArg Prod.fst p) ▸ (mem_filter.mp (mem_filter.mp h).1).2))
 have hB(k:ℕ)(i:Link V)(g: i∈ livelies V)(f:originSum i.1=k)(j:G.ColorIndex): |v (⟨i,g⟩,j)| ≤ (k:ℝ)*Z:=by
    induction k using Nat.strong_induction_on generalizing i with
    | h k ih=>
      obtain ⟨s,p⟩:= mem_filter.mp g; have ht:Active i:= (mem_filter.mp s).2; obtain ⟨x,b⟩:=i
      let l:= tooth (x,b) ht; have hv:l < b:= live_mark p ht; let y:=x-step l; obtain ⟨h₁,h₂,m⟩:= live_pins x b p ht
      let X:= smear e *ᵥ v
      have h':X ((y+step b,l),j)=0:=hp _ _ h₂.1 (fun e=> e.1 h₂); have hh:X ((y,l),j)=0:=hp _ _ h₁.1 (fun e=> e.1 h₁)
      have hr: X ((x,b),j)=v (⟨(x,b),g⟩,j):= smear_t (e:=e) v (⟨(x,b),g⟩,j) -- tune inference
      let R:=mark (x,b) ht; have hl:v (⟨(x,b),g⟩,j)=X ((y,b),j)+faceCurl R u j:=by
        rw [←hr,show faceCurl R u j= _ from atCurl G X j _]; unfold R Curl mark PlaqAxes.ordered; change X ((x,b),j)=X ((y,b),j)+(X ((y,min b l),j)+X ((y+step (min b l),max b l),j)-(X ((y+step (max b l),min b l),j)+ X ((y,max b l),j))); rw [min_eq_right hv.le,max_eq_left hv.le,h',hh,show y+step l=x from sub_add_cancel ..]; ring
      have hu: |faceCurl R u j|≤ Z:=by
         rw [←sq_le_sq₀ (abs_nonneg _) hx,sq_abs,show Z^2=inCurl G u from Real.sq_sqrt he]; apply le_trans (b:=‖faceCurl R u‖^2) _ (single_le_sum (f:=fun i=>‖faceCurl i u‖^2) (fun _ _=>sq_nonneg _) (mark_ort (x,b) p ht)); rw [pts]; exact single_le_sum (f:=fun i=>(faceCurl R u i)^2) (fun _ _=>sq_nonneg _) (mem_univ j)
      have hy: originSum y+1=k:= (reduced x l (tooth_spec _ ht).2.1).trans f
      have hv: |X ((y,b),j)| ≤ (originSum y:ℕ)*Z:=by
         by_cases e':Active (y,b); · have h:(y,b)∈ livelies V:= mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,e'⟩,m⟩; rw [show X ((y,b),j)=v (⟨(y,b),h⟩,j) from smear_t (e:=e) v (⟨(y,b),h⟩,j)]; exact ih _ (by omega) _ _ rfl
         rw [show X ((y,b),j)=0 from hp (y,b) j m e',abs_zero]; exact mul_nonneg (by positivity) hx
      rw [hl]; exact (abs_add_le ..).trans ((add_le_add hv hu).trans_eq (by rw [← hy]; push_cast; ring))
 rw [grit]; refine (sum_le_sum (g:=fun _: E_=> ((limit V :ℕ)* Z)^2) ?_).trans ?_
 · intro i hi; rw [← sq_abs]; refine pow_le_pow_left₀ (abs_nonneg _) (le_trans (hB _ i.1.val i.1.property rfl i.2) ?_) 2; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (origin_lt_w _).le) hx
 rw [sum_const,card_univ,nsmul_eq_mul,mul_pow,show Z^2= inCurl G u from Real.sq_sqrt he]; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (by unfold hatp; linarith only [mul_le_mul_of_nonneg_right (count_f G V) (show 0 ≤ ((limit V:ℕ):ℝ)^2 by positivity)]) he

theorem screenP (V:Side) : (DueQ G W D B V).PosDef ∧ spanD (DueQ G W D B V) (p.direct/hatp G V):=by
 have hr:=p.quadratic_pos; have hx:0< hatp G V:=by unfold hatp; positivity
 have h:spanD (DueQ G W D B V) (p.direct/hatp G V):=by
    intro v; have hp:=shrine G (V:=V) v; rw [show dotProduct v _=p.direct*_+_ from ledgerQ G W D B v]; refine le_trans ?_ (le_add_of_nonneg_right (sum_nonneg (fun _ _=> sq_nonneg _))); exact (mul_le_mul_of_nonneg_right hp (by positivity : 0≤p.direct/hatp G V)).trans_eq (by field_simp)
 exact ⟨psd (clearQ ..) (fun v t=>(mul_pos (show 0<dotProduct v v from (by simpa using (PosDef.one (n:=Fresco G V) (R:=ℝ)).dotProduct_mulVec_pos t)) (show 0 < p.direct/hatp G V by positivity)).trans_le (h v)),h⟩
end YM.CF.Papyrus.Mosaic
#print axioms YM.CF.Papyrus.Mosaic.screenP
