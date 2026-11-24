import YM.SU5.Exchange.Pipe.Raw

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n

/-! Short kernels from the pipeline, including transported ones,
are bounded local continuous matrices on Openc with an *a priori* small support. -/

variable {o: Seat n} {k:ℕ} {a b d:ℝ} {X:SOp n}

/-- Move a truncated expansion along a given Sweep, retaining all three budgets,
the Openc identity, and the home-site cutoff. -/
lemma trunk_move (p:Trunk o X k a b d)(s:Sweep n):
    Trunk (boxA s o) (julStep s X) k a (Tenant.quota^2*b) d:=by
 refine ⟨jul_sells s p.pay,?_⟩
 obtain ⟨F,W,h,t,c,m⟩:=p.home
 let Q:Sa n≃Sa n:=Equiv.finsetCongr (boxA s⁻¹).symm
 have hQ(S):Q S=actY s⁻¹ S:=rfl
 let A(S:Sa n):=Mx s d (F (Q.symm S))
 let B(S:Sa n):=noteU s⁻¹ (W (Q.symm S))
 have hA(S):A (Q S)=Mx s d (F S):=by simp [A]
 have hB(S):B (Q S)=noteU s⁻¹ (W S):=by simp [B]
 have hu(S): (Q S).card=S.card:=card_map ..
 refine ⟨A,B,?_,?_,?_,?_⟩
 · intro T; obtain ⟨S,rfl⟩:=Q.surjective T; rw [hA,hB,hQ]; exact mini _ _ _ _ (h _)
 · intro T; obtain ⟨S,rfl⟩:=Q.surjective T; rw [hB,hu]; intro v
   have w:W S≠0:=by
     intro f; apply v; rw [f]; ext; simp [noteU]
   refine ⟨?_,(t S w).2⟩
   simp [hQ,actY,sitU,(t S w).1]
 · let D:=quota
   have hx:0 ≤ D:= le_trans (by norm_num: (0:ℝ)≤16) quota_bound
   rw [← Equiv.sum_comp Q]
   apply le_trans _ (mul_le_mul_of_nonneg_left c (sq_nonneg D)); rw [mul_sum]
   apply sum_le_sum; intro i _
   rw [hB,Branch.rent,hu,mul_left_comm]
   apply mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
   unfold noteU ledgerV; simp_rw [normU,mul_sum]
   let L(x y j k:I):= jLL s⁻¹ x j*jLL s⁻¹ y k*W i j k
   change ∑ x:I,∑ y:I,∑ j:I,∑ k:I,L x y j k ≤ _
   simp_rw [sum_comm (f:=fun y (j:I)=> ∑ k:I,L _ y j k)]
   rw [sum_comm]; apply sum_le_sum; intro j _; simp_rw [sum_comm (f:=fun y k=> L _ y j k)]; rw [sum_comm]; apply sum_le_sum; intro l _
   unfold L; simp_rw [←Finset.sum_mul,←Finset.mul_sum]; rw [←Finset.sum_mul]
   refine mul_le_mul_of_nonneg_right ?_ ((h i).nonn _ _); exact (mul_le_mul (ρ_K ..) (ρ_K ..) (sum_nonneg fun t _=>norm_nonneg _) hx).trans_eq (by ring)
 intro x; let z:=Sour.fog s d x
 change ech s⁻¹ (X z.val)= _; rw [m z]; unfold ech; rw [singT,win_sum,map_sum,←Equiv.sum_comp Q (fun S=>A S x)]
 simp_rw [hA]; rfl

lemma trunk_go (u x:Site n) (p:Trunk (node u) X k a b d):
    Trunk (node x) (co_Ψ x u X) k a (Tenant.quota^2*b) d:=by
 unfold co_Ψ; convert trunk_move p (taxiPlus (x-u)) using 1
 rw [platforms,add_sub_cancel]

-- l^1 charges will also give uniform bounds for convergence of extracted
-- stencils; the varying periods need not have compatible trunks.
variable {T S:Sa n}{L:Toll I}
local notation "O"=>Openc (More n) d
local notation "D" => (↥(Openc (More n) d))
/-- The extraneous radius payment can be forgotten. -/
private lemma trench (W:Sa n→Toll I) (p:∑ S:Sa n,rent a S*ledgerV (W S) ≤ b)
    (h:∀ S i j,0≤ W S i j) (ha:0≤a): ∑ S:Sa n,ledgerV (W S) ≤ b:=by
 refine le_trans (sum_le_sum fun S _=>?_) p
 refine le_mul_of_one_le_left (sum_nonneg fun i _=>sum_nonneg fun j _=> h S i j) (Branch.rent_one ha _)

lemma soak_sum (h:Soak o X a b d)(t:D)(ha:0≤a): (∑ i:I,∑ j:I,‖X t.val i j‖) ≤ b:=by
 obtain ⟨F,W,p,_,l,u⟩:=h; rw [u]
 calc
   _ ≤ ∑ i:I, ∑ j:I, ∑ S:Sa n, W S i j := by
      apply sum_le_sum; intro i _; apply sum_le_sum; intro j _
      rw [Matrix.sum_apply]; exact (norm_sum_le ..).trans (sum_le_sum fun S _=>((p S).expo i j).bounded _)
   _ = ∑ S:Sa n, ledgerV (W S):=by simp_rw [ledgerV,sum_comm (f:=fun (j:I) (S:Sa n)=> _)]
   _ ≤ b:= trench W l (fun S=> (p S).nonn) ha
lemma soak_trace (h:Soak o X a b d)(t:D)(ha:0≤a):
    ‖(X t.val).trace‖ ≤ b:= by
  refine (norm_sum_le univ (fun i:I=>X t.val i i)).trans (le_trans ?_ (soak_sum h t ha))
  exact sum_le_sum fun i _=> single_le_sum (f:=fun j=>‖X t.val i j‖) (fun _ _=>norm_nonneg _) (mem_univ i)
lemma soak_cont (h:Soak o X a b d): Continuous fun x:D=>X x.val:=by
 obtain ⟨F,W,l,t,u,e⟩:=h
 rw [funext e]; exact continuous_finsetSum _ (fun i _=> (l i).cont)

abbrev rayG (n:Side)(d:ℝ)(g:Seat n→E):Openc (More n) d→Openc (More n) d:=(forum n d).drive g

lemma soak_frame (h:Soak o X a b d)(t:D)(g:Seat n→E):
   X (rayG n d g t).val=twist (tradew n g) (X t.val):=by
 obtain ⟨F,W,l,p,r,v⟩:=h; rw [v,v,map_sum]
 apply sum_congr rfl; intro S _
 exact (l S).frame.frame g _
abbrev purse (k:ℕ)(o:Seat n):Sa n:=halo k {o}

variable (p:Trunk o X k a b d)
private lemma bound_grove (l:Grove (terr (More n)) S)(m:o∈S)(g:S.card<k):
    S⊆purse k o:=by
 intro i r; apply halo_spec.mpr
 -- check orientation
 exact ⟨o,mem_singleton_self _,((l.lim o m i r).trans g).le⟩
lemma trunk_lives (p:Trunk o X k a b d)(t:D)(i j:I)(v:X t.val i j ≠ 0) :
    node i.1.1 ∈ purse k o ∧ node j.1.1 ∈ purse k o:=by
 obtain ⟨F,W,h,t0,_,r⟩:=p.home; rw [r,Matrix.sum_apply] at v
 obtain ⟨S,hS⟩:∃ S,W S i j≠0:=by
   by_contra! h0; apply v; apply sum_eq_zero; intro S _
   have hu:=((h S).expo i j).bounded t
   rw [h0] at hu; exact norm_le_zero_iff.mp hu
 obtain ⟨l,x,y⟩:=((h S).expo i j).triggered hS
 have hW:W S≠0:=by intro e; rw [e] at hS; exact hS rfl
 obtain ⟨m,f⟩:=t0 S hW
 exact ⟨bound_grove l m f x,bound_grove l m f y⟩
/-- A short kernel is uniformly Lipschitz per entry, paying only
for profile changes on the ball, irrespective of other distant flags. -/
lemma trunk_lip (p:Trunk o X k a b d)(ha:0≤a)(x y:D)(i j:I):
   ‖X x.val i j-X y.val i j‖ ≤ b*(fare (purse k o) x.val y.val/|d|):=by
 obtain ⟨F,W,h,l,u,v⟩:=p.home
 let δ:=fare (purse k o) x.val y.val/|d|
 have g:0≤δ:=div_nonneg (fare_t ..) (abs_nonneg _)
 apply le_trans _ (mul_le_mul_of_nonneg_right (trench W u (fun S=> (h S).nonn) ha) g)
 rw [v,v,Matrix.sum_apply,Matrix.sum_apply,←sum_sub_distrib,sum_mul] -- sum_mul
 refine (norm_sum_le ..).trans (sum_le_sum fun S _=>?_ )
 have hn:= (h S).nonn
 have q:W S i j ≤ ledgerV (W S):=(single_le_sum (fun j _=>hn i j) (mem_univ j)).trans
   (single_le_sum (f:=fun i=>∑ j:I,W S i j) (fun i _=> sum_nonneg fun j _=>hn i j) (mem_univ i))
 refine le_trans (((h S).expo i j).variation x y) (le_trans ?_ (mul_le_mul_of_nonneg_right q g))
 by_cases hp: W S=0
 · simp [hp]
 obtain ⟨hu,hv⟩:=l S hp
 apply mul_le_mul_of_nonneg_left _ (hn i j)
 exact div_le_div_of_nonneg_right (fare_inc (bound_grove (f_then (h S) hp) hu hv) _ _) (abs_nonneg d)

lemma trunk_local (p:Trunk o X k a b d)(ha:0≤a)(x y:D)(h: fare (purse k o) x.val y.val=0):
    X x.val=X y.val:=by
 ext i j
 have hh:=trunk_lip p ha x y i j; rw [h,zero_div,mul_zero] at hh
 exact sub_eq_zero.mp (norm_le_zero_iff.mp hh)

lemma fare_vanish {U V:Pane n}(h:Agrees S U V):
    fare S (profile U) (profile V)=0:=by
 unfold fare; apply sum_eq_zero; intro i hi
 obtain ⟨_,v,u⟩:=mem_filter.mp hi
 have e:profile U i=profile V i:=by unfold profile; rw [h i v u]
 rw [e,sub_self,norm_zero]

end YM.CF.Merino

