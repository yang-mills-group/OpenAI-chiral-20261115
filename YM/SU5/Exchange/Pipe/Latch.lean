import YM.SU5.Exchange.Pipe.Travel
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}
local notation "Ω"=> Single N
-- uniform S op transport
abbrev julStep(s:Sweep N)(V:SOp N) : SOp N:=fun x=> ech s⁻¹ (V (Levier.gateC s.charge (castX s) x))
lemma jul_sells (s:Sweep N)(p:Soak o X a v d):Soak ((boxA s) o) (julStep s X) a (Tenant.quota^2*v) d:=by
 obtain ⟨F,W,v1,l,u,k⟩:=p
 let Q:= actY s⁻¹; let A:= noteU s⁻¹; let V(T):=Mx s d (F T); let B(T): Toll Ω:= A (W T); let D:=quota; have hx:0 ≤ D:= le_trans (by norm_num: (0:ℝ)≤16) quota_bound
 refine arm_v Q V B (fun i=> mini _ _ _ _ (v1 i)) ?_ ?_ ?_
 · apply le_trans _ (mul_le_mul_of_nonneg_left u (sq_nonneg D)); rw [mul_sum]; apply sum_le_sum; intro i _
   rw [Branch.rent,show (Q i).card=i.card from card_map ..,mul_left_comm]
   apply mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
   unfold B A noteU ledgerV; simp_rw [normU,mul_sum]
   let L(x y j k:Ω):= jLL s⁻¹ x j*jLL s⁻¹ y k*W i j k
   change ∑ x:Ω,∑ y:Ω,∑ j:Ω,∑ k:Ω,L x y j k ≤ _
   simp_rw [sum_comm (f:=fun y (j:Ω)=> ∑ k:Ω,L _ y j k)]
   rw [sum_comm]; apply sum_le_sum; intro j _; simp_rw [sum_comm (f:=fun y k=> L _ y j k)]; rw [sum_comm]; apply sum_le_sum; intro k _
   unfold L; simp_rw [←Finset.sum_mul,←Finset.mul_sum]; rw [←Finset.sum_mul]
   refine mul_le_mul_of_nonneg_right ?_ ((v1 i).nonn _ _); exact (mul_le_mul (ρ_K ..) (ρ_K ..) (sum_nonneg fun t _=>norm_nonneg _) hx).trans_eq (by ring)
 · intro i g; have hu:o∉ i:=by contrapose! g; simp [Q,actY,sitU,g]
   unfold B A noteU; rw [l i hu]; ext; simp
 · intro x; let z:=Sour.fog s d x
   change ech s⁻¹ (X z.val)= _; rw [k z]; unfold ech; rw [singT,win_sum,map_sum]; rfl
lemma julius (s:Sweep N) (X:SOp N)(V:Pane N):ech s (julStep s X (profile V))= X (profile (flashA s V)):=by rw [julStep,Sour.paceK,inv_mul_cancel,beat_x, flashA, Levier.veil_p]

-- Trunks. For a given component, with full ledger b charged at root; retain also independent
-- smaller-size physical payload outside Craft from those same pieces. Trunk enforces ALWAYS on that Germ only.
structure Trunk (o:Seat N)(Y:SOp N)(k:ℕ)(a b d:ℝ): Prop where
 pay: Soak o Y a b d
 home: ∃ (F:Sa N→Raw (Openc (More N) d) (Single N))(C:Sa N→Toll (Single N)), (∀ S,Suite (badge _) (bail N d) (bail N d) S (C S) (F S)) ∧ (∀ S,C S≠0 → o∈ S ∧ S.card< k) ∧ (∑ S:Sa N,rent a S*ledgerV (C S)) ≤ b ∧ ∀ x:Openc (More N) d,Y x.val= ∑ S:Sa N,F S x
lemma f_then {F:Raw (Openc (More N) d) (Single N)}{C:Toll (Single N)}{S:Sa N}(p:Suite (badge _) (bail N d) (bail N d) S C F)(x:C≠0) : Grove (terr _) S:=by
 obtain ⟨a,b,h⟩:∃ a b,C a b≠0:=by by_contra! h; exact x (funext fun a=>funext fun b=>h a b)
 exact ((p.expo a b).triggered h).1
lemma cut_tr (k:ℕ)(p:Soak o X (a+a) b d)(u:0<a): ∃ Y Z:SOp N, Trunk o Y k a b d ∧ Soak o Z a (Real.exp (-a*k)*b) d∧ ∀ U:Openc (More N) d, X U.val= Y U.val+Z U.val:=by
 obtain ⟨F,C,q,t,r,v⟩:=p
 let W(S:Sa N):=if S.card<k then F S else (0:Raw (Openc (More N) d) (Single N)); let B(S: Sa N):= if S.card<k then C S else (0:Toll (Single N)); let W'(S:Sa N):= if S.card<k then 0 else F S; let B'(S:Sa N):=if S.card<k then 0 else C S
 let Y(x:Chin N):Op Ω:=if h:x∈ Openc (More N) d then ∑ S:Sa N,W S ⟨x,h⟩ else 0
 let Z(x:Chin N):Op Ω:=if h:x∈ Openc (More N) d then ∑ S:Sa N,W' S ⟨x,h⟩ else 0
 have ht (x:Openc (More N) d):Y x.val= ∑ S:Sa N,W S x:=dif_pos x.property
 have hv(x:Openc (More N) d):Z x.val= ∑ S:Sa N,W' S x:=dif_pos x.property
 have hp(S:Sa N):Suite (badge _) (bail N d) (bail N d) S (B S) (W S):=by unfold B W; split; exact q S; exact Suite.free _
 have hg(S:Sa N)(g':o∉ S):B S=0:=by unfold B; split; exact t S g'; rfl
 have hk(S:Sa N) : 0 ≤ledgerV (C S):=sum_nonneg fun i _=>sum_nonneg fun j _=> (q S).nonn _ _
 have hx : (∑ S:Sa N,rent a S*ledgerV (B S))≤ b:=by
    refine le_trans (sum_le_sum (fun i _=>?_)) r; unfold B; split_ifs; exact mul_le_mul_of_nonneg_right (Branch.rent_up (le_add_of_nonneg_right u.le) _) (hk _); simp [ledgerV]; exact mul_nonneg (rent_pos _ _).le (hk _) -- simp may change ledger
 refine ⟨Y,Z,⟨⟨W,B,hp,hg,hx,ht⟩,W,B,hp,fun S c=> ⟨Classical.not_not.mp (mt (hg S) c),?_⟩,hx,ht⟩,?_,fun U=>?_⟩
 · by_contra! p; exact c (if_neg (not_lt.mpr p))
 · refine ⟨W',B',fun i=>?_ , fun S p=>?_ ,?_ ,hv⟩
   · unfold W' B'; split; exact Suite.free _; exact q _
   · unfold B'; split; rfl; exact t _ p
   apply le_trans _ (mul_le_mul_of_nonneg_left r (Real.exp_pos _).le); rw [mul_sum]; apply sum_le_sum; intro S _
   unfold B'; split_ifs with p
   · rw [show ledgerV (0:Toll Ω)=0 from by simp [Branch.ledgerV],mul_zero]; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (rent_pos _ _).le (hk _))
   rw [←mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ (hk _); unfold Branch.rent; rw [←Real.exp_add]; apply Real.exp_le_exp.mpr
   have he: (k:ℝ)≤ S.card:=Nat.cast_le.mpr (by omega); nlinarith
 rw [v U,ht,hv,←sum_add_distrib]; apply sum_congr rfl; intro S _; unfold W W'; split <;> simp

end YM.CF.Swell
