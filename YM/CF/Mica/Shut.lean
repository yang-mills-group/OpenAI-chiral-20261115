import YM.CF.Mica.Sleet
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Beau
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
open Ione Larch
open Taxi Geo RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
local notation "Hz"=> Scree.Hub n
open Trees
open Salt
variable {Z':Scree.Hub n} {F: InkD n}(s:Sweep n)
local notation "Op"=> Z'.val.1
local notation "mV"=> moveHub s Z'
-- Echo part.A. restore any rank0 sweep
abbrev τR(s:Sweep n):Sweep n:=⟨s.s,s.b,false⟩
abbrev τV(s:Sweep n):Sweep n:=⟨1,0,s.charge⟩
lemma sash : τR s * τV s=s:=by change Sweep.mk (s.s*1) (s.b+ s.s.act 0) (false.xor s.charge)= _; simp
lemma cupE(i:Hz):moveHub (τV s) i=i:=by
 let T:= (τV s); have ht:boxA T= Equiv.refl _:= Equiv.ext fun i=>by rw [sitA]; change affine 1 ((assembly n).root 0) i=i; rw [map_zero]; simp [affine]
 refine Subtype.ext (Prod.ext ?_ ?_); change (boxA T).symm _=_; rw [ht]; rfl; change Finset.map (boxA T).symm.toEmbedding _=_; rw [ht]; ext; simp
lemma warP(i:tangD n): flashA (τV s) (increment 1 i)= increment 1 (cape_v s.charge i):=by
 rw [revoke]; change polarT _ ∘ Lattice.pull 1 ((assembly n).root 0) (increment _ _) =_; rw [map_zero,pull_id,Ione.high_c]; exact congrArg (fun v:Pane n=> increment v _) (funext fun i=> map_one _)
lemma path_v(i:tangD n)(a:IsAffineDirection Op i)(b:Bool): IsAffineDirection Op (cape_v b i):=by
 cases b; exact a; obtain ⟨v,rfl⟩:= (LinearJet.isAffine ..).mp a; let w: LinearJet E' := ⟨fun i=> Reef.frolic (v.at0 i),fun i j=> Reef.frolic (v.slope i j)⟩
 refine (LinearJet.isAffine ..).mpr ⟨w,?_⟩; funext i; unfold LinearJet.field; change Reef.frolic (v.at0 _ + ∑ j:Axis, coord (Z'.val.1) i.1 j • v.slope i.2 j) = _; simp only [map_add,map_sum,map_smul]; rfl
lemma turn_z (p:PressB P Z' F h d)(t:spark Op F)(u:0≤ h): spark Op (step_F (τV s) (sage_L F)):=by
 constructor; · rw [solute_A,Facet.glacial,t.1,map_zero]
 intro x y a b; let L:=cast_B (wageZ (τV s)⁻¹); let Z:tangD n→L[ℝ] tangD n:= cape_v s.charge; let θ:=Taxi.lifeH F ∘ increment 1; let X:=pot (∅:Finset (Dwell n)); let G:=step_F (τV s) (sage_L F); have he: X ∘ G ∘ increment 1=(L∘ θ)∘Z:= funext fun i=>by change pot ∅ (step_F (τV s) (sage_L F) _)=_; rw [solute_A,warP]; rfl
 change iteratedFDeriv ℝ 2 (X ∘ G ∘ increment 1) 0 _= _; let M:Fin 2→ DN:= ![x,y]; rw [he,jets_linear (k:=2) Z (L.contDiff.contDiffAt.comp 0 (profit p u)), L.iteratedFDeriv_comp_left (f:=θ) (profit p u) le_rfl]
 change L (iteratedFDeriv ℝ 2 θ 0 fun i=> Z (M i))=0; rw [show (fun i=> Z (M i))= (![Z x,Z y]: Fin 2→ DN) from funext fun i=>by fin_cases i<;>rfl]; exact (congrArg L (t.2 _ _ (path_v (Z':=Z') x a _) (path_v (Z':=Z') y b _))).trans (map_zero _)
lemma spell_t (V: RegBudget n): base_Q (τR s) (base_Q (τV s) V) = base_Q s V:=by funext i x; simp only [base_Q,step_F,Function.comp_apply,step_k,Spire.lights,moon_Y,sash]; rw [←mul_inv_rev,sash]
lemma statV{u : RegBudget n}(l:ℕ) (p:IncX (fun _=>False) u P h a)(v:Ionic P l u)(x:0≤h)(t:4 ≤ (More n).val):Ionic P l (base_Q s (cry_H u)):=by
 rw [←spell_t]; obtain ⟨K,w,h⟩:=p.weight; intro F y z; let V:=moveHub (τR s) F; have hg: Pave P l V.val.2:= (dawnZ ..).1 (show chute P l F from z); have hv: Nonwrapping V.val.2 V.val.1:=by obtain ⟨p,h⟩:=chart_p (τR s) F; rw [p,h,spin_wrap] at y; exact y -- tune
 let U:=u V; let Y:=step_F (τV s) (sage_L U); have hY: sage_L Y=Y:=by
    funext i; change wage_Q 0 (suit_Y (τV s)⁻¹ (wage_Q 0 _))=_; rw [show wage_Q 0 (suit_Y _ _) = _ from pose_U ..]; refine congrArg (suit_Y _) ?_; refine pimp_Q _ _ fun i=>?_ ; simp_rw [price_X]; split<;>rename_i z<;>simp only [Function.comp_apply,sage_L,price_X]<;>first|rw [if_neg z]|rw [if_pos z]
 change spark F.val.1 (step_F (τR s) (step_F (τV s) (sage_L (u (moveHub (τV s) V)))))
 rw [cupE]; change spark F.val.1 (step_F _ Y); nth_rw 1 [←hY]; exact spark_A (τR s) (swirl_x P (τV s) V _ ((cupE s V).symm ▸ (show PressB P V U _ _ from w V)) x) (turn_z (Z':=V) s (w V) (v V hv hg) x) t x rfl hv
lemma head0 (V:RegBudget n)(k:ℕ):Ionic P k (head_L V):=by
 intro i p t; let F:=head_L V i; have he(x :Pane n):pot ∅ (F x)=0:=by change crumb (blind_E _).val ∅= _; exact (shelter_Q _ _).trans (if_pos card_empty)
 refine ⟨he _,fun a b g v=>?_⟩; rw [show pot ∅ ∘ head_L V i ∘ increment 1=(fun _=> (0:ℂ)) from funext fun i=>he _, iteratedFDeriv_const_of_ne (by omega: (2:ℕ) ≠ 0)]; rfl
lemma hale_Q{V:RegBudget n}(q:IncX (fun _=>False) V P h b)(v:Ionic P m V)(x:0≤h)(w:4 ≤ (More n).val)(t:Sym_P (head_L V)): Ionic P m (writ_E V):=by
 have hy:head_L V+cry_H V=V:= funext fun i=> funext fun j=> sub_add_cancel ..; nth_rw 1 [←hy]; rw [writ_k,sure_c _ t]; let C':=shine_M P.order P.power*b; let Z(i:Sweep n):= base_Q i (cry_H V); have he(i):IncX (fun _=>False) (Z i) P h C':= thrive_X _ _ q x
 let A₀:= ∑ i:Sweep n,Z i; have hz:=ton_W P Z (fun _=>C') he univ
 have hr:Ionic P m A₀:=by
    choose A v' j using fun i=>(he i).weight; intro X t k; unfold A₀; rw [Finset.sum_apply]; exact add_Z (X₀:=X) _ _ (fun i=> A i X) (fun i _=> statV i m q v x w X t k) (fun i _=> v' i X) x -- tune args
 exact wage_add (head0 V m) (night_k hr x hz _) (share_V P V q) (thin_P P A₀ _ hz) x
end YM.CF.Beau
