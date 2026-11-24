import YM.SU5.FiniteGaugeData.Mist.Dairy
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace Mist
open KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
local notation "D"=> Decko Y h a
variable (H:Harbor Y h W' R Φ a)(x y:Decko Y h a)
local notation "Λ₀"=> (A a)
namespace Dover
variable (X:Engine Y h W' R a H)(q:Carousel Λ.R.L)
-- tapes with variable height on entries
variable {σ:Type}(s':σ→ℕ)(d':σ→ℕ)(p:∀ x,0<d' x)(x':σ→ W (tent Y h))(v':∀ x, Plan Y h a (d' x) (x' x))(S₁:σ→Carousel Λ.R.L)
def office (x:σ):=spinT Λ.R.L (s' x) (d' x)
#check office
abbrev HiPlay (i:σ) := bitOp Y h (s' i) W' R A S' a (d' i) H (v' i) (p i)
local notation "ℓ" i:max => s' i
local notation "d₀"=>office (Λ:=Λ) s' d'
local notation "M"=> H.space
local notation "Q"=> HiPlay Y h W' R A S' a H s' d' p x' v'
local notation "A₁" j:max=> ascended Y h (s' j) W' R (k-s' j) (x' j)
local notation "U" i:max=> S₁ i a
abbrev canopy (k:ℕ)(x:σ):=ascended Y h (s' x) W' R (k-s' x) (x' x)
abbrev signal (i j:σ) := (regular Y h W' R a H X ((↑((S₁ j) a)-↑((S₁ i) a) - (office (Λ:=Λ) s' d' i)).toNNReal)) * (spireT X.val (S₁ j-S₁ i))
-- h:o exact stamp.P.We use less strict .≥ variant first.
def stage (i j:σ):Prop:= (↑((S₁ i) a):ℝ)+(office (Λ:=Λ) s' d' i) ≤ ↑((S₁ j) a)
abbrev CastEconomy (i j:σ):Prop:= (↑((S₁ i) a):ℝ)+(office (Λ:=Λ) s' d' i) < ↑((S₁ j) a)
variable (F:σ→Four ℤ)(Z:List σ)(K:Calibration) -- finite promotion positions
abbrev apparent (i:σ)(t:Four ℤ):= orbitW Kₜ (F i-t) (canopy Y h W' R s' x' k i) -- args check
local notation "Γ"=> signal Y h W' R a H X s' d' S₁
local notation "W0"=> (omegaV Y h W' R a H)
local notation "ϕ"=> apparent Y h k W' R s' x' F
private lemma horizon_eq (i j:σ)(u:S₁ i=reportQ k (F i))(v:S₁ j=reportQ k (F j)) : ((S₁ j a):ℝ)-((S₁ i a):ℝ)= spinT Λ.R.L k ((F j-F i) a):=by rw [u,v]; change spinT _ k (F j a)-spinT _ k (F i a)=spinT _ k (F j a - F i a); rw [sub_eq_add_neg (F j a),slot_add,slot_neg,sub_eq_add_neg]
-- current relative stencil computed on true larger Town
set_option maxHeartbeats 680000 in
lemma pay_leg (i j:σ)(g:stage (Λ:=Λ) a s' d' S₁ i j)(u:S₁ i=reportQ k (F i))(v:S₁ j=reportQ k (F j))(t:s' i≤ k) : ∃ y:Decko Y h a,(HiPlay Y h W' R A S' a H s' d' p x' v' i) ((signal Y h W' R a H X s' d' S₁ i j) (H.leaf k x))= H.leaf k y ∧ y.val = canopy Y h W' R s' x' k i * orbitW Kₜ (F j-F i) x.val:=by
    have hc := horizon_eq -- tune # declaration
       (Λ:=Λ) k a S₁ F i j u v
    obtain ⟨n,rfl⟩:= Nat.exists_eq_add_of_le t; unfold canopy; simp_rw [Nat.add_sub_cancel_left]; have hz:(d₀) i ≤ spinT Λ.R.L (s' i+n) ((F j-F i) a):=hc ▸ (le_sub_iff_add_le'.mpr g)
    obtain ⟨y,a1,b⟩:= appointment Y h (s' i) W' R A S' a (d' i) n H x (F j-F i) X (x' i) (v' i) (p i) hz; refine ⟨y,?_,b⟩
    let L:= regular Y h W' R a H X ((spinT Λ.R.L (s' i+n) ((F j-F i) a)- (office (Λ:=Λ) s' d' i)).toNNReal) * spireT X.val (reportQ (s' i+n) (F j-F i)); have he : (Γ) i j=L:=by
         unfold signal L; apply congrArg₂ (·*·); · rw [hc]
         exact congrArg (spireT X.val) (by rw [u,v, report_sub])
    refine Eq.trans (congrArg ((Q) i) (DFunLike.congr_fun he (H.leaf _ x))) a1
#check apparent
include X S'
lemma pay_final (i:σ)(t:s' i ≤ k) :∃ y:Decko Y h a,(HiPlay Y h W' R A S' a H s' d' p x' v' i) (W0)= H.leaf k y ∧ y.val = canopy Y h W' R s' x' k i:=by
 obtain ⟨n,rfl⟩:= Nat.exists_eq_add_of_le t; let j:=s' i+n; let Ω:=H.leaf j 1; let T:= bitOp Y h (s' i) W' R A S' a (d' i) H (v' i) (p i); exact ⟨appointed Y h _ a (d' i) n W' R (v' i) 1,(congrArg T (gold_leaf Y h W' R a H j).symm).trans (bitPlus Y h _ W' R A S' a (d' i) n H 1 (v' i) (p i)), by rw [appointed_val,Swing,show (1:D).val=1 from rfl,clock_one,mul_one]; unfold canopy; rw [Nat.add_sub_cancel_left]⟩
def sees (t:Four ℤ):= (Z.map fun i=> (apparent Y h k W' R s' x' F i t)).prod
omit X S' in
lemma sees_adv (t u:Four ℤ): orbitW Kₜ (u-t) (sees Y h k W' R s' x' F Z u)=sees Y h k W' R s' x' F Z t:=by unfold sees; rw [sailing,List.map_map]; apply congrArg (fun f:σ→W Kₜ=> (Z.map f).prod); funext i;  unfold Function.comp apparent; rw [orbitW_add]; rw [show u-t+(F i-u)=F i-t from by abel]
abbrev Membership (Z:List σ)(S₁:σ→Carousel Λ.R.L) :Prop:=∀ i∈Z,s' i≤k ∧ S₁ i=reportQ k (F i)
set_option maxHeartbeats 520000 in
lemma orbital (i:σ)(z':Membership (Λ:=Λ) k s' F (i::Z) S₁)(c:(i::Z).Pairwise (stage (Λ:=Λ) a s' d' S₁)) :∃ z:Decko Y h a,spool (Q) (Γ) i Z (W0)= H.leaf k z ∧ z.val=sees Y h k W' R s' x' F (i::Z) (F i):=by -- shadow x' rename
 induction Z generalizing i with
 | nil=>
    obtain ⟨x,v,w⟩:= pay_final Y h k W' R A S' a H X s' d' p x' v' i (z' i (by simp)).1; refine ⟨x,v,?_⟩; rw [w,sees,List.map_cons,List.prod_cons]; simp only [apparent,sub_self,orbitW_o,List.map_nil,List.prod_nil,mul_one]
 | cons j z ih=>
    obtain ⟨y,v,w⟩:= ih j (fun x t=> z' x (List.mem_cons_of_mem _ t)) (List.pairwise_cons.mp c).2; obtain ⟨t,zP,wP⟩:= pay_leg Y h k W' R A S' a H y X s' d' p x' v' S₁ F i j ((List.pairwise_cons.mp c).1 j (by simp)) (z' i (by simp)).2 (z' j (by simp)).2 (z' i (by simp)).1
    refine ⟨t,Eq.trans (congrArg (fun s=>(Q) i (((Γ) i j) s)) v) zP,?_⟩; rw [wP,w,sees_adv Y h k W' R s' x' F (j::z)]; unfold sees; simp only [List.map_cons, List.prod_cons]; -- unfolds twice; careful Γ parser
    nth_rw 1 [show (ϕ) i (F i)=(A₁ i) from (by unfold apparent; rw [sub_self,orbitW_o])] -- tune nth.
def aspect:= inner ℂ (W0) (TapeT (Q) (Γ) Z (W0))
#check aspect
lemma sold (z':Membership (Λ:=Λ) k s' F Z S₁)(c:Z.Pairwise (stage (Λ:=Λ) a s' d' S₁))(o:Four ℤ): aspect Y h W' R A S' a H X s' d' p x' v' S₁ Z=Φ k (sees Y h k W' R s' x' F Z o):=by
 cases Z
 case nil=>
                change inner ℂ (W0) (W0)= Φ k 1; rw [inner_self_eq_norm_sq_to_K,omegaBudget Y h W' R A S' a H]; rw [S'.living]; simp

 case cons i Z=>
                 obtain ⟨x,v,u⟩:= orbital Y h k W' R A S' a H X s' d' p x' v' S₁ F Z i z' c; refine Eq.trans (congrArg (inner ℂ (W0)) v) ((goldPrice Y h k W' R a H x).trans ((congrArg (Φ k) u).trans ?_)); -- orientation
                 -- mangle
                 exact ((cross_paid Y h k W' R A S' (F i-o) (sees Y h k W' R s' x' F (i::Z) (F i))).symm.trans (congrArg (Φ k) (sees_adv Y h k W' R s' x' F (i::Z) o (F i))))
omit S' X in
lemma possible : ∀ᶠ k:ℕ in atTop, ∃ F:σ→Four ℤ,Membership (Λ:=Λ) k s' F Z S₁:=by
 classical
 filter_upwards [(eventually_all_finset (I:=Z.toFinset)).mpr (fun i _=> (report_often (S₁ i)).and (eventually_ge_atTop (s' i)))] with k p
 have he(i:σ):∃ v:Four ℤ,i∈ Z →s' i≤ k ∧ S₁ i=reportQ k v:=by
      by_cases h:i∈Z; · obtain ⟨⟨z,u⟩,v⟩:=p i (List.mem_toFinset.mpr h); exact ⟨z,fun _=> ⟨v,u⟩⟩
      exact ⟨0,fun t=>(h t).elim⟩
 choose F h using he; exact ⟨F,h⟩
omit X S' in
lemma sees_permute {Z':List σ}(t:Z.Perm Z')(o:Four ℤ): sees Y h k W' R s' x' F Z o=sees Y h k W' R s' x' F Z' o:=by
 letI:CommMonoid (W Kₜ):= { (inferInstance: Monoid (W Kₜ)) with mul_comm a b:= commW Kₜ a b }; exact (t.map _).prod_eq -- cl.H
#check Sphere
end Dover
end Mist
end YM.CF.Buffered.Afterglow.Hierarchy
