import YM.SU5.FiniteGaugeData.Signal.CurtainCall
import YM.SU5.FiniteGaugeData.Signal.Noon
/-! # Greenhouse inclusion on larger envelope retaining charge.
 Verifies intrinsic `FIRST` only dependence and nonzero even when INHIBITING flat fields on
 plaquette based at one of the charged nodes. No lower on such curvature in level s units
 as `s→∞`; default curvature shrinks in signed currency. We specify native `τ>0`.
 Includes bill loading on all local outcomes.
 -/
set_option autoImplicit false
set_option linter.flexible false
set_option maxHeartbeats 760000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Signal
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Afterglow Buffered.Advance Reef Hom Tenant Branch Buffered.Concord Buffered.Afterglow.Satin Lifted
open MeasureTheory Push.SectorMeasure Girt
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate Pointwise
attribute [local instance] opCStarAlgebra
open Supplies Sparkle Sparkle.Condense Sparkle.Portage Sparkle.Circuit Pastel Momentum Furnace
open Scherzo Kinetic Play Py Py.Rate LocalLimit Preparation Skyscraper IgnoreFog Vale Period
open Buffered.Reliance Buffered.Reliance.ShortWave Afterglow Afterglow.Journey
open Boon Graph Pressure Esti Jade.Earn Phase CF.Laic CF.Ember
open Escalator Concord Boon Parfume
namespace Showcasing
open Scherzo.Parfume Ovation Concord
variable {K:Calibration}{S T V:Finset Cover} {i j:ℕ} (L:List Cover) {a c:ℝ}
variable (f: LinksC→ℂ)(h:Soft S f)
include h
lemma soft_mul {g:LinksC→ℂ}(p:Soft S g): Soft S (f*g) := ⟨env_mult h.env p.env,fun x y p'=> congrArg₂ (·*·) (h.localV x y p') (p.localV x y p')⟩
lemma softUp (t:S⊆T): Soft T f := ⟨h.env,fun x y q=>h.localV x y (fun i a b=> q i (t a) (t b))⟩
omit h
variable (K)
lemma stuccM (g:LinksC→ℂ): stucco K f*stucco K g=stucco K (f*g) := by
 funext n i; change (f _ • (1:FC (Single (K.c n)))) * (g _ • (1:FC (Single (K.c n))))=(f _*g _) • (1:FC (Single (K.c n))); rw [mul_smul, Algebra.smul_mul_assoc, one_mul]
variable {x:junior K}(l:SU.Slot)
include h
lemma glowThrough {L:List Cover}{U:Finset Cover}{x:Buffered.Family K} (p:x∈ Flying K (family l) U S L) : stucco K f*x ∈ Flying K (family l) U S L:=by
 induction p using Submodule.span_induction with
 | mem x p=> obtain ⟨g,t,v,u,rfl⟩:= p; exact Submodule.subset_span ⟨f*g,soft_mul f h t,v,u,by rw [←mul_assoc,stuccM]⟩ -- order
 | zero=> rw [mul_zero]; exact Submodule.zero_mem _
 | add x y e p u v=> rw [mul_add]; exact Submodule.add_mem _ u v
 | smul a x u v=> rw [Algebra.mul_smul_comm]; exact Submodule.smul_mem _ _ v
omit h
include K
lemma upgrade (p:S⊆T)(t:Effect K l V S L x): Effect K l V T L x:=by
 have hK: Flying K (family l) V S L≤Flying K (family l) V T L:=by apply Submodule.span_mono; intro i v; obtain ⟨f,h,x,p,rfl⟩:=v; exact ⟨f,softUp f h (by assumption),x,p,rfl⟩
 exact ⟨hK t.wild, lodge K _ p t.opera,t.key⟩
lemma lifted (t:Effect K l V T L x)(p:Face ℤ)(v:restsOn {p} T)(c:ℝ): Effect K l V T L (visible K p v c x):=by
 let f(x:LinksC):= suspend {p} c (x,1); let z:= ablate {p} c K v; let h:=toll ({p}:Finset _) c v; let J:=club K T
 have hs:Soft T f:= by
    refine ⟨Env.along (g:=fun x:LinksC=>(x,(1:LinksC))) h.env (measurable_id.prodMk measurable_const),fun x y v=> h.locus (x,1) (y,1) v fun _ _ _=>rfl⟩
 exact ⟨glowThrough K f hs l t.wild,J.mul_mem (clamp_pay {p} c v) t.opera,(singlets K).mul_mem (toll_sing {p} c v) t.key⟩ -- order conf
-- world readability mark at nonflat. p chosen centered at nodeC
variable {K}
def ticket (x:Cover):Face ℤ:= (nodeC x,⟨(0,1),by decide⟩)
def plock (x:Cover) : Finset Cover:= List.toFinset (visits (nodeC x) (square 0 1))
def path (p:List Cover)(T:Finset Cover) : Finset Cover:= T ∪ p.toFinset.biUnion plock
omit K
lemma rentTicket {J:List Cover}{x:Cover} (p:x∈ J): restsOn {ticket x} (path J T):= by simp only [restsOn,mem_singleton,forall_eq]; exact Subset.trans (subset_biUnion_of_mem plock (List.mem_toFinset.mpr p)) subset_union_right
include K
lemma shelf (h:Shelter T V L)(v:starboard 3 0 K.ℓ T): starboard 3 0 K.ℓ (path L T):=by
 intro i p; rcases mem_union.mp p with p|p; · exact v i p
 obtain ⟨i',t,k⟩:= mem_biUnion.mp p
 have hw:= v (nodeC i') (h.2.1 i' (List.mem_toFinset.mp t)); rw [show i 3=nodeC i' 3 from ?_]; exact hw
 unfold plock at k; simp [visits,square] at k; rcases k with (k|k|k|k|k); all_goals subst i; norm_num [step_apply, show (3:Axis)≠1 by decide, show (3:Axis)≠0 by decide]
omit K
lemma shelterUp (h:S⊆T)(p:Shelter S V L):Shelter T V L :=⟨fun i x=> h (p.1 i x),fun i x=> h (p.2.1 i x),p.2.2⟩

structure Radiance (C a:ℝ)(K:Calibration)(T S:Finset Cover)(J:List Cover) (E':ℕ→ Buffered.Family K→ℂ) : Prop where
 gain : MixedMean C a K T S J E'
 leftmost : ∀ᶠ s:ℕ in atTop,∀ l:SU.Slot,∃ i:List Cover,i.Sublist J ∧ ∃ (p:Cover),p ∈ i ∧ restsOn {ticket p} T ∧ ∃ (f:junior K), Effect K l S T i f∧ a < ‖E' s f.val‖ ∧ (∀ m:Side,∀ x, ‖f.val m x‖ ≤ C) ∧ (∃ n:ℕ, ∀ m:Side,∀ x:Fields (K.c m),SU.group.chord (faceValue (onC _ x.1) (ticket p))< Meter n → f.val m x=0)

variable {P:Preparation}{k' l':ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l'))(H:Real.exp 1 ≤ P.x)
variable {i k:ℕ→ℕ}{I:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}{E':ℕ→Buffered.Family (tent Y H)→ℂ}
local notation "Λ"=> tent Y H
variable {Q:Playhouse P l'}(W:Traced Y H i k I E' Q)
include W
lemma marquee {C a:ℝ}{J:List Cover} (h:MixedMean C a (tent Y H) T S J E'): Radiance C a (tent Y H) (path J T) S J E':=by
 let V:= path J T
 refine ⟨⟨shelf J h.house h.pose,shelterUp _ subset_union_left h.house,h.cost,h.gain,h.earn.mono (fun s x l=>?_)⟩, ?_⟩ -- arg order
 · obtain ⟨i,p,q,f,v,a',e'⟩:=x l; exact ⟨i,p,q,f,upgrade _ _ l subset_union_left v,a',e'⟩
 filter_upwards [h.earn] with s f l; obtain ⟨L,u,v,x,t,q,e⟩:= f l; obtain ⟨i,p⟩:= List.exists_mem_of_ne_nil _ v -- tune shadow
 let H':= ticket i
 have v':restsOn {ticket i} (path J T):=rentTicket (u.subset p)
 let w(n:ℕ):= visible (tent Y H) H' v' (Meter n) x; let q₀:Effect (tent Y H) l S (path J T) L x:= upgrade _ _ l subset_union_left t
 obtain ⟨n,r⟩:= ((maintained (ticket i) Y H s v' W x q₀.opera h.cost e).norm.eventually (lt_mem_nhds q)).exists
 refine ⟨L,u,i,p,v',w n,lifted _ _ _ q₀ (ticket i) v' (Meter n),r,(fun m v=> shining (tent Y H) (ticket i) h.cost v' (e m) (Meter n) v), n,fun m x h=>?_⟩; unfold w; rw [visible_view,if_neg (not_le_of_gt h)]
end Showcasing
end YM.CF.Signal
#print axioms YM.CF.Signal.Showcasing.marquee
