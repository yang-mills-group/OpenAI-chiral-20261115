import YM.CF.Tye.Lens
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Valve
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tye
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
open Affine Reine
open Gauges PhysicalNext.InteractingRank Rink Tye Corne Cloak
local notation "Ω"=> RG.Atom SU.group
variable {s' n':Side} {t e:ℝ}
lemma un_v(U:Config G c)(i:Site c)(j:Site c)(V:Ω n): V.unmasked (Lattice.translate j U) i=V.unmasked U (i+j):=by unfold RG.Atom.unmasked; simp_rw [Work.F03.atSite_path,translated_face,slot_shift,translated_travel]
lemma sends(j b:Site c)(z:Cell c) : shiftFaces 1 b z=Channels.shift b PlaqAxes z:= by
 apply Prod.ext; show Face.lower z 1 b=_; rw [Pump.lowers (1,b)]; simp [Pump.off]; rfl; change PlaqAxes.rotate _ _=z.2; apply Subtype.ext; unfold PlaqAxes.rotate PlaqAxes.ordered; have h:= z.2.property; simp [min_eq_left h.le,max_eq_right h.le] -- tune
abbrev Ah(z: Site c)(X:Support c):= X.image fun w=>w+z
lemma tour_s (j b:Site c)(W:Ω n) : W.footprint (j+b)=Ah b (W.footprint j):=by unfold RG.Atom.footprint Ah; rw [image_image]; apply image_congr; intro i z; dsimp only [Function.comp_apply]; abel
lemma tour_f (b:Site c)(z:Cell c): touched (Channels.shift b PlaqAxes z)= Ah b (touched z):=by rw [← sends b b]; change touched (Face.send 1 b z)= _; simp only [Work.H03.touched_send]; congr 1
lemma toll_v(U:Config G c)(i:Cell c)(b:Site c):Pressure.toll (Lattice.translate b U) i=Pressure.toll U (Channels.shift b PlaqAxes i):=by rw [Pressure.toll,translated_face]; rfl
lemma codA(X:Support c)(b:Site c)(i:Cell c): i∈costA X↔ Channels.shift b PlaqAxes i∈costA (Ah b X):=by
 simp only [Cloak.costA,mem_filter,mem_univ,true_and,tour_f,Finset.not_disjoint_iff,Ah]; simp only [mem_image]; constructor
 · rintro ⟨j,p,g⟩; exact ⟨j+b,⟨j,p,rfl⟩,j,g,rfl⟩
 rintro ⟨j,⟨k,p,rfl⟩,w,g,t⟩; rw [add_right_cancel t] at g; exact ⟨_,p,g⟩
lemma taxes(M: Stores S)(s t:Signed)(b:Site c)(i:Cell f): i∈ (turnStore t (Locations.book s b M)).costs↔ Channels.shift (S.ratio.embed (Channels.offset s b t)) PlaqAxes i∈(turnStore (s*t) M).costs:=by
 let V:=S.ratio.embed b; let W:= Channels.offset s b t; let B:=S.ratio.embed W
 rw [costs_turn,costs_turn, ← sends B]; change _∈Finset.map _ _↔ _; rw [mem_map_equiv]; change Face.send s V (Face.send t 0 i)∈_↔ Face.send (s*t) 0 (Face.send 1 B i)∈_
 have he: Pump.meet (s,V) (t,(0:Site f))=Pump.meet (s*t,(0:Site f)) (1,B):=by
    have hp:S.ratio.embed W=Channels.offset s V t:= (Channels.offset_fine ..).symm
    unfold B; rw [hp]; unfold Pump.meet Channels.offset affine; simp only [Signed.act_zero,zero_add, add_zero,mul_one,Signed.act_inv]
 exact (show Face.send s V (Face.send t 0 i)=Face.send (s*t) 0 (Face.send 1 B i) by rw [Pump.tracks (s,V) (t,0), he]; exact (Pump.tracks (s*t,0) (1,B) i).symm) ▸ Iff.rfl -- tune rw
lemma toured(M: Stores S)(s t: Signed)(b:Site c)(i:Cell c): i∈ traceZ (turnStore t (Locations.book s b M)).flags ↔ Channels.shift (Channels.offset s b t) _ i∈ traceZ (turnStore (s*t) M).flags:=by
 simp only [traceZ,mem_filter,mem_univ,true_and,flag_turn]; change _∈Finset.map _ _↔ _; rw [mem_map_equiv]; change affine s b (t.act i.1)∈_ ↔ (s*t).act (i.1+Channels.offset s b t)∈ _; simp only [Signed.act_add,Channels.offset, Signed.act_inv]; unfold affine; rw [Signed.act_mul] -- tune
-- applies to ALL rotated pockets
section
variable (A B:Finset (Cell c)) (b:Site c) (X: Support c) (U: Config G c)(V:Ω n)(P:PathData G)(Q:Clip)
local notation "F"=> Channels.shift b PlaqAxes
variable (p:∀ i:Cell c,i∈A↔ (Channels.shift b PlaqAxes) i∈B)
local notation "G'"=> Lattice.translate b U
include p
lemma pol_t : polP t G' X A↔ polP t U (Ah b X) B:= by
 constructor
 · intro x i z; obtain ⟨j,rfl⟩:=(F).surjective i; have he:= mem_inter.mp z; exact ((toll_v U j b).symm.trans_le (x _ (mem_inter.mpr ⟨(p j).2 he.1,(codA _ b j).2 he.2⟩)))
 intro x i z; have he:=mem_inter.mp z; rw [toll_v]; exact x _ (mem_inter.mpr ⟨(p i).1 he.1,(codA _ b i).1 he.2⟩)
lemma nose_t: nose q e A X G'= nose q e B (Ah b X) U:=by
 let D:=Cloak.costA X \ A; let D':=Cloak.costA (Ah b X) \ B
 have hx(i:Cell c): i∈ D↔ F i∈D':= Finset.mem_sdiff.trans ((and_congr (codA X b i) (not_congr (p i))).trans Finset.mem_sdiff.symm)
 change shutters _ _ D _=shutters _ _ D' _; refine Finset.prod_equiv (show Cell c≃Cell c from F) hx fun i _=> ?_; rw [toll_v]
lemma lush_t(i:Site c): lush_k q V A t i G'=lush_k q V B t (i+b) U:=by unfold lush_k; rw [un_v]; unfold east; rw [tour_s, pol_t A B b _ U p]; split; rw [nose_t A B b _ U p]; rfl
lemma peer_t(i:Site c): peer_k V A t i G'=peer_k V B t (i+b) U:=by unfold peer_k; rw [tour_s, pol_t A B b _ U p]; split; rw [un_v]; rfl
lemma pers_t(i:Site c): pers A Q t G' i↔ pers B Q t U (i+b):=by
 constructor
 · intro z u g; obtain ⟨v,rfl⟩:=(F).surjective u; have he:= z v ((p v).2 g); rw [translated_face] at he; rw [show (F v).1=v.1+b from rfl,separation_translate]; exact he
 intro z u g; have he:= z (F u) ((p u).1 g); rw [show (F u).1=u.1+b from rfl,separation_translate] at he; rw [translated_face]; exact he
lemma path_t(i:Site c)(W:Ω n): sleeve W A Q i t G'= sleeve W B Q (i+b) t U:= by unfold sleeve; rw [pers_t _ _ _ _ _ p]; split; exact un_v ..; rfl
lemma king_t (r u:ℕ)(i:Cell c): Esti.king A P Q r u t G' i= Esti.king B P Q r u t U (F i):=by
 let W:=Lattice.translate b U; unfold Esti.king hallP taken; simp only [ite_true]; simp only [p]; rw [Pressure.toll, translated_face, pers_t A B b U Q p i.1,translated_plot]; rfl -- tune unfolding Pressure.toll
end
end YM.CF.Tye
