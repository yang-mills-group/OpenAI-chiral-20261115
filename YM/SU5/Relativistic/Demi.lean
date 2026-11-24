import YM.SU5.Relativistic.Malt
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
variable (G: Gauge){V:Side}
local notation "J"=> Fresco G W_
local notation "H_"=> Ink G N
local notation "Fσ"=> Face (Per N)
variable (W:PathData G)(D:ℕ)
variable {a b σ C' P:ℝ}{K:Bed}{c:Clip}(B:W.Bounds c σ C' P)
include B
lemma hearth (L:Ratio C N)(g:2≤ C.val)(v:2≤ N.val)(f:Floor K c N a b)(t:Attached K W): let Ψ:=loadP (hess G K N) (sheet L G.ColorIndex); Ψ.PosDef ∧ Ψ.det=costDet G K N:=by
 intro T; have h:T.det=costDet G K N:=(marksG L _ g v).invariance (grates N v) (e:=Embedding.subtype _) (g:= fast G N) (by ext x; simp) (by ext x; simp [fast,ScrollB]) (hess_symm G K f) (hess_ker ..)
 refine ⟨?_,h⟩
 have ht: (hess G K N).PosSemidef:=PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_iff_isSymm.mpr (hess_symm G K f)) (fun x=> by
    rw [star_trivial,tent_h,metric_pair K B t _ _ f]; have he:= c.quadratic_pos; exact Finset.sum_nonneg fun _ _=> add_nonneg (mul_nonneg he.le real_inner_self_nonneg) real_inner_self_nonneg)
 exact (ht.submatrix (fun i:↥(sheet L G.ColorIndex)=> i.val)).posDef_iff_det_ne_zero.mpr ((show T.det≠0 from h.symm ▸ ((fairDet G K v f B t).1.det_pos.ne' : costDet G K N≠0))) -- tune
variable {r :ℝ}(he:0<r)(f:Floor K c N a b)(t:Attached K W)(x:(1+1/r)*vane σ C' D≤r*c.direct)
include he f t x
lemma rim_price (p:T_)(v:J→ℝ) : let R:= (hess G K N).submatrix (porto L G p) (porto L G p); dotProduct v (R*ᵥ v)≤ (1+r)*dotProduct v (DueQ G W D B W_ *ᵥ v)+(∑ i∈outlays L G D, v i^2)*Berry c C' r:=by
 intro X; rw [show dotProduct v _= _ from shade (porto L G p) (hess G K N) v v]
 apply (expense G W D B r he _ f t x).trans
 let U:= porto L G p; let F:=drafts G U v; let w:= brightQ G W_ v
 let y:= bridle L G D v; let t':=smear U *ᵥ y; let s:= drafts G U y; let Z:= ∑ i∈ outlays L G D,v i^2
 let T:=mounted L p; let M:= plumage L D p
 let d(g:fieldDir G N 1)(i:Fσ):=‖faceCurl i g‖^2
 let b(g:fieldDir G N 1)(i:Fσ):=‖cropL G W D g i‖^2
 have hp: dotProduct t' t'=Z:= (grant_sq U y).trans (shroud L G D v)
 have ht : curlE F≤ inCurl G w+96*Z:=by
   change (∑ i:Fσ,d F i)≤_; rw [←sum_add_sum_compl T, show ∑ i∈ T,d F i= _ from gate_cr L G p v]; apply add_le_add_right
   rw [show ∑ i∈ Tᶜ,d F i= ∑ i∈ Tᶜ,d s i from Finset.sum_congr rfl (fun i h=>by unfold d; rw [show faceCurl i F= _ from dark_curl L G p D v i (mem_compl.mp h)])]; exact le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=> sq_nonneg _)) ((hull_q G t').trans_eq (by rw [hp]))
 have hx : ∑ i:Fσ,b F i≤ shortV G W D w+6*C'^2*96*Z:=by
   rw [←sum_add_sum_compl M,show ∑ i∈M,b F i= _ from gate_row L G W D p v]; apply add_le_add_right
   rw [show ∑ i∈ Mᶜ,b F i=∑ i∈ Mᶜ,b s i from Finset.sum_congr rfl fun i h=>by unfold b; rw [show cropL G W D F i= _ from dark_row L G W D p v i (mem_compl.mp h)]]; exact le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>sq_nonneg _)) ((combC G W D B t').trans_eq (by rw [hp]))
 rw [show dotProduct v (DueQ G W D B W_ *ᵥ v)= _ from ledgerQ G W D B v]; apply le_trans (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left ht c.quadratic_pos.le) hx) (show 0≤1+r by positivity)); change _ ≤ (1+r)*(c.direct*inCurl G w+shortV G W D w)+Z*Berry c C' r; unfold Berry; linarith only [show 0≤ Z from sum_nonneg fun _ _=> sq_nonneg _]

local notation "σD"=> sheet L G.ColorIndex
local notation "κ"=> Berry c C' r
def shootB(p:T_):= brick L p ×ˢ(univ:Finset G.ColorIndex)
omit he f t x B in
lemma sail_s (p:T_)(i:H_): i∈ shootB L G p↔ ∃ x,porto L G p x=i:=by
 constructor; · intro t; obtain ⟨j,u,g⟩:=mem_image.mp (mem_product.mp t).1; exact ⟨(⟨j,u⟩,i.2),Prod.ext g rfl⟩
 rintro ⟨x,rfl⟩; exact mem_product.mpr ⟨mem_image_of_mem (raise L p) x.1.property,mem_univ _⟩
omit he f t x B in
lemma sail_v(p:T_): shootB L G p⊆ σD:= Finset.product_subset_product (brick_v L p) (Finset.Subset.refl _)
abbrev Runt(p:Clip)(G:Gauge)(V:Side):=p.direct/hatp G V
def priceB (G:Gauge)(σ C' r:ℝ)(p:Clip)(n:Side)(D:ℕ)(i:PathData G){P:ℝ}(x:i.Bounds p σ C' P):ℝ:= (1+r)^Fintype.card (Fresco G n)*(DueQ G i D x n).det * (1+Berry p C' r / Runt p G n)^(32*(2*D+2)*n.val^3*Fintype.card G.ColorIndex)
lemma factor (h:2≤ C.val)(q:2≤ N.val)(p:T_): (loadP (hess G K N) (shootB L G p)).det ≤ priceB G σ C' r c W_ D W B:=by
 have hf:0< c.direct:= c.quadratic_pos; have he':0<1+r:=by positivity
 have hv:0≤κ:=by unfold Berry; positivity
 let S:=shootB L G p; have H: (loadP (hess G K N) S).PosDef:= included (sail_v L G p) (hearth G W B L h q f t|>.1)
 have hp: ((hess G K N).submatrix (porto L G p) (porto L G p)).PosDef:=by
    let u(i:J):↥S:=⟨porto L G p i,(sail_s L G _ _).mpr ⟨i,rfl⟩⟩
    exact H.submatrix (e:=u) (fun i j e=> (porto L G p).injective (congrArg (fun i:↥S=>i.val) e))
 rw [letter _ _ (sail_s L G p)]
 let A:= DueQ G W D B W_; let q:= (1+r) • A; let Z:= outlays L G D
 have hl:= screenP G W D B W_
 have ht:q.PosDef:=hl.1.smul he'
 have hz:spanD q (Runt c G W_):= fun v=> by
    apply (hl.2 v).trans; unfold q; rw [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]; apply le_mul_of_one_le_left _ (by linarith); simpa using hl.1.posSemidef.dotProduct_mulVec_nonneg v
 have hy:= packed Z hv
 refine (det_hike hp (ht.add_posSemidef hy) ?_).trans ?_
 · intro v; rw [Matrix.add_mulVec,dotProduct_add,plaque_p,show dotProduct v (q*ᵥ v) = _ from (show dotProduct v (q*ᵥ v)=(1+r)*dotProduct v (A*ᵥ v) from (by unfold q; rw [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]))]; exact rim_price L G W D B he f t x p v
 have hu:0<Runt c G W_:=by unfold Runt hatp; positivity
 apply (plaza q ht hu hv hz Z).trans; unfold priceB; rw [show (1+r)^Fintype.card (Fresco G W_)*(DueQ G W D B W_).det=q.det from (det_smul ..).symm]
 refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ?_ (out_card L G D)) ht.det_pos.le; exact le_add_of_nonneg_right (div_nonneg hv hu.le)
def boundD (G:Gauge)(C:Side)(V:Side)(c:Clip)(σ C' r:ℝ)(D:ℕ)(W:PathData G){P:ℝ}(p:W.Bounds c σ C' P) := (priceB G σ C' r c V D W p)^(C.val^4)* (Berry c C' r)^(4*C.val^4*V.val^3*Fintype.card G.ColorIndex)
lemma bulky (h:2≤ C.val)(p:2≤N.val): costDet G K N ≤ boundD G C W_ c σ C' r D W B:=by
 let S:= shootB L G; let H:= (univ:Finset (Site C)).biUnion S; let w:= wires L ×ˢ (univ:Finset G.ColorIndex); let T:= hess G K N
 have ht:H= batchIn L ×ˢ (univ:Finset G.ColorIndex):=by unfold H batchIn S shootB; ext j; simp
 have hx:σD=H ∪ w:=by rw [ht]; unfold sheet w; ext i; simp only [mem_union,mem_product,mem_univ,true_and,and_true]; rw [←vivot L]; simp only [mem_union,or_comm]
 have hz:w.card ≤ 4*C.val^4*L.count.val^3*Fintype.card G.ColorIndex:=by unfold w; rw [card_product,card_univ]; exact Nat.mul_le_mul_right _ (woolV L)
 have hp: H⊆ σD:=by rw [hx]; exact subset_union_left
 have he': w⊆ σD:=by rw [hx]; exact subset_union_right
 have hm: Disjoint H w:=by rw [ht,Finset.disjoint_left]; intro j i g; exact (mem_sdiff.mp (mem_product.mp g).1).2 ((mem_product.mp i).1)
 have hf:= c.quadratic_pos; have hg: 1 ≤ κ:=by unfold Berry; have hp:0≤ (1+r)*(c.direct*96+6*C'^2*96):=(by positivity); linarith
 obtain ⟨u,U⟩:= hearth G W B L h p f t
 rw [←U]; apply (cutBloc T _ _ _ hx hm u).trans
 have hv:= included he' u; have ho: (loadP T w).det ≤ κ^(4*C.val^4*L.count.val^3*Fintype.card G.ColorIndex):=by
   let s:= (κ) • (1: Matrix w w ℝ); have hh:s.PosDef:=(PosDef.one).smul (zero_lt_one.trans_le hg); refine (det_hike hv hh ?_).trans ?_
   · intro v; unfold s; rw [Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,smul_eq_mul]; let e:↥w ↪ H_:=Embedding.subtype _; change dotProduct v (T.submatrix e e *ᵥ v)≤_; rw [show dotProduct v (_*ᵥ v)= _ from shade e T v v,←grant_sq e v]; exact expense_p G W D B r he _ f t x -- tune
   rw [show s.det=κ^w.card from (by unfold s; rw [det_smul,det_one,mul_one,Fintype.card_coe])]; exact pow_le_pow_right₀ hg hz
 have hh:(loadP T H).det≤ (priceB G σ C' r c W_ D W B)^(C.val^4):=by
   refine (boardwalk T _ u univ S ?_ hp).trans ((Finset.prod_le_prod ?_ (fun i _=>factor L G W D B he f t x h p i)).trans_eq ?_)
   · intro i v b w e; exact Finset.disjoint_left.mpr fun {x} y z=> Finset.disjoint_left.mp (mitt_d L i b e) (brick_in L i ((mem_product.mp y).1)) (brick_in L b ((mem_product.mp z).1))
   · intro i _; exact (included (sail_v L G i) u).det_pos.le
   rw [prod_const,card_univ,Lattice.site_card]
 exact mul_le_mul hh ho hv.det_pos.le ((included hp u).det_pos.le.trans hh)
end YM.CF.Papyrus.Mosaic
#print axioms YM.CF.Papyrus.Mosaic.bulky
