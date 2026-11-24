import YM.CF.Tarn.Tuck
import YM.CF.Facet.Horn
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rink
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reef
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
variable {K:Teller G}
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
variable (T:Tube G S)(x:ℝ)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)(s:Signed)(b:Site c)(g:Site c → SU.group.El)
section
variable (M:Monk G S)
variable (h:K.Funds S T)(p:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hm:0 < m)(hf:120 ≤ radiusB x)
section
local notation "F"=>clue S s b M
abbrev page :ColorOrtho G (Bond f):=fiber s b M.V S
abbrev canE:= calendar x M.key M.park s b
local notation "O"=>page s b M
local notation "U"=>canE x s b M
include h
lemma blank_c: liftN T x (F).V (F).k (F).key (F).park q d ((F).bush x) l= Orthogonal.move (onBond O) (U).onKey (liftN T x M.V M.k M.key M.park q d (M.bush x) l):=by
 obtain ⟨v,w,hT,Q⟩:=h.feeds; rw [← h.high] at hT; rw [show (F).bush x=_ from gen x S s b M]; exact boxL (Char.turned T M.key M.park x M.V M.k q d (M.bush x) s b hT (funds_branch h)) (fun e=>green_map ..) (funds_branch h) hT
include p hm hf
lemma beam_c: pushP T (F).key (F).park (F).V (F).k q d x ((F).bush x) l ((F).bell x) =Orthogonal.move (onBond O) (U).onKey (pushP T M.key M.park M.V M.k q d x (M.bush x) l (M.bell x)):=by
 obtain ⟨σ,a,H,A⟩:=h.feeds; rw [← h.high] at H
 have he: credW T (F).key (F).park (F).k q d x ((F).bush _) l (F).V= Orthogonal.warp (onBond O) (U).onKey (credW T M.key M.park M.k q d x (M.bush _) l M.V):= by
    rw [show (F).bush x=_ from gen x S s b M]; exact Neige.Nature (Char.turned T M.key M.park x M.V M.k q d (M.bush x) s b H (funds_branch h)) (fun e=> green_map ..) l H (funds_branch h) p hm hf
 have hh: tape.symm ((F).bell x)= Orthogonal.move (onBond O) (U).onKey (tape.symm (M.bell x)):=by apply tape.injective; funext i; erw [move_tape,tape.apply_symm_apply,tape.apply_symm_apply]; rfl
 unfold pushP; rw [hh,he]; exact warp_mv (onBond O) (U).onKey _ _
lemma space_f : (F).fuel x T q d l β=Orthogonal.move (onBond O) (U).onKey (M.fuel x T q d l β):=by
 change _+ coupling β • pushP _ _ _ _ _ _ _ _ _ _ _=_; rw [blank_c T x q d l s b M h,beam_c T x q d l s b M h p hm hf]; exact windM ..
lemma space_s: (F).sent x T q d l β=pull s (S.ratio.embed b) (M.sent x T q d l β):=by change landed _ _ _ _ _ ((F).fuel x T q d l β)=_; rw [space_f T x q d l β s b M h p hm hf]; exact spike ..
end
section
local notation "F"=>shiftZ g M
local notation "O"=> Gauges.rotating (constantGauge g S.ratio)
local notation "U"=> PhysicalNext.OrderedAffine2B.SymRows.room x M.key M.park
include h p hm hf
lemma gauge_b:pushP T (F).key (F).park (F).V (F).k q d x ((F).bush x) l ((F).bell x)= Pogo g M x (pushP T M.key M.park M.V M.k q d x (M.bush x) l (M.bell x)):=by
 obtain ⟨σ,a,H,A⟩:=h.feeds; rw [← h.high] at H
 have he:credW T (F).key (F).park (F).k q d x ((F).bush _) l (F).V=Orthogonal.warp (onBond O) (U).onKey (credW T M.key M.park M.k q d x (M.bush _) l M.V):= Neige.Nature (gaugeH T M.key M.park x M.V M.k q d (M.bush x) g H (funds_branch h)) (fun _=> Iff.rfl) l H (funds_branch h) p hm hf
 have hh:tape.symm ((F).bell x)= Pogo g M x (tape.symm (M.bell x)):=by apply tape.injective; funext i; erw [move_tape,tape.apply_symm_apply,tape.apply_symm_apply]; rfl
 unfold pushP; rw [hh,he]; exact warp_mv (onBond O) (U).onKey ..
lemma gauge_s:(F).sent x T q d l β=Lattice.gauge (constantGauge g S.ratio) (M.sent x T q d l β):=by
 change landed x M.key M.park (Lattice.gauge g M.V) (Gauges.gaugeY g x M.key M.park (M.bush x)) ((F).fuel x T q d l β)=_; rw [Slate.buzz g M q x β d h l m p hm hf]; exact audU g M x _ _
end
section
abbrev cedar : Monk G S:= {M with V:=Reef.echo M.V,U:=Reef.echo M.U,z:=Tensor.lifting (Char.shiftF _) (Equiv.refl _) M.z}
local notation "F"=>cedar M
local notation "O"=> Char.shiftF (Bond f)
local notation "U"=> PhysicalNext.OrderedAffine2B.SymRows.room x M.key M.park
lemma echo_l(a: Prices SU.group (Active M.key x M.park)):
 landed x M.key M.park (F).V ((F).bush x) (Orthogonal.move (onBond O) (U).onKey a)=Reef.echo (landed x M.key M.park M.V (M.bush x) a):=by
 ext1 i; by_cases hi:i∈ M.park.trunks
 · have ht(e: LinkArray G M.park.Free): M.park.drape e i=1:= M.park.on_tree _ ⟨i,hi⟩; unfold landed Next.SectorChange.physical; change M.park.drape _ i=qG (M.park.drape _ i); rw [ht,ht,map_one]
 let j:M.park.Free:=⟨i,hi⟩; unfold landed Next.SectorChange.physical
 change M.park.drape _ j.val=qG (M.park.drape _ j.val); rw [M.park.off_tree,M.park.off_tree]; unfold Next.SectorChange.returned thaw; by_cases hi':chill M.key x M.park j
 · let t: Frozen M.key x M.park:= ⟨j,hi'⟩; rw [show j=t.val from rfl,freeze_held,freeze_held]; rfl
 let t:Active M.key x M.park:=⟨j,hi'⟩; rw [show j=t.val from rfl,freeze_regular, freeze_regular]; unfold release; rw [move_tape]; change SU.group.lieExp (Reef.frolic (tape a t)) * replica S.ratio (Reef.echo M.V) t.val.val=qG _; rw [repE, cool_a,map_mul]
variable (ht: Reef.Rare T.up)
include h ht
lemma echo_c:liftN T x (F).V (F).k (F).key (F).park q d ((F).bush x) l= Orthogonal.move (onBond O) (U).onKey (liftN T x M.V M.k M.key M.park q d (M.bush x) l):=by
 obtain ⟨v,w,hT,Q⟩:=h.feeds; rw [← h.high] at hT; exact boxL (storyE T _ _ _ _ _ _ _ _ (funds_branch h) hT ht) (fun _=> Iff.rfl) (funds_branch h) hT
include p hm hf
lemma echo_b:pushP T (F).key (F).park (F).V (F).k q d x ((F).bush x) l ((F).bell x)= Orthogonal.move (onBond O) (U).onKey (pushP T M.key M.park M.V M.k q d x (M.bush x) l (M.bell x)):=by
 obtain ⟨σ,a,H,A⟩:=h.feeds; rw [← h.high] at H
 have he: credW T (F).key (F).park (F).k q d x ((F).bush _) l (F).V=Orthogonal.warp (onBond O) (U).onKey (credW T M.key M.park M.k q d x (M.bush _) l M.V):= Neige.Nature (storyE T _ _ _ _ _ _ _ _ (funds_branch h) H ht) (fun _=> Iff.rfl) l H (funds_branch h) p hm hf
 have hh:tape.symm ((F).bell x)= Orthogonal.move (onBond O) (U).onKey (tape.symm (M.bell x)):=by apply tape.injective; funext i; erw [move_tape,tape.apply_symm_apply,tape.apply_symm_apply]; rfl
 unfold pushP; rw [hh,he,warp_mv]
lemma echo_f:(F).fuel x T q d l β=Orthogonal.move (onBond O) (U).onKey (M.fuel x T q d l β):=by change _+coupling β • pushP _ _ _ _ _ _ _ _ _ _ _=_; rw [echo_c T x q d l M h ht,echo_b T x q d l M h p hm hf ht]; exact windM ..
lemma echo_s:(F).sent x T q d l β=Reef.echo (M.sent x T q d l β):=by change landed _ _ _ _ _ ((F).fuel x T q d l β)=_; rw [echo_f T x q d l β M h p hm hf ht]; exact echo_l x M (M.fuel x T q d l β)
end
end
end YM.CF.Rink
