import YM.CF.Salt.Piers
import YM.CF.Haro.Tacit
import YM.CF.Salt.Milk
import YM.CF.Salt.Desk
import YM.CF.Plume.Wager
import YM.CF.Haro.Silk
import YM.CF.Salt.Felt
import YM.CF.Tye.Wheel
import YM.CF.Salt.Dial
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 21000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Salt
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake Scion Levier Hive Nacre Tye Skye RG Pressure Next.SectorChange Planned.AtomRegular Girt Spire
open Eire Skye Levier Scion Urn Pastry Rill Kennel Pec
open Eire Girt Tulip Spire Proa RG Pressure Stilo Scree Palot Tye Cour Broc Hive Hake
open Esti Forge AnalyticBridge.Annulus1AD Ac AnalyticBridge.GaussianFieldAlignment Tensor Locations Push.SectorMeasure.Oriented
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure Slate Atala
variable {P N B:Side}{G:Ratio (mid N B) (mid P B)}(S:StepData (Domain N B) (Domain P B))(x:ℝ)(t:S.ratio=ratio G)(s:Sweep (mid N B))(A:Stores S)(V:Pane (mid P B))(X:Support (Domain P B))
local notation "ζ"=> shiftFaces s.s (S.ratio.embed (Facet.pasta s))
local notation "T"=> reSweep G s
lemma pay_l(i: Cell (Domain P B)):i∈ (airport s A).costs↔ ζ i∈A.costs:=mem_map_equiv
include t
lemma mimeA : Facet.pasta (reSweep G s)=S.ratio.embed (Facet.pasta s):=by rw [←sew_b,←sew_b,t]; exact (reA ..).symm -- include
include t
lemma helve (W:Pane (mid P B)): flashA (reSweep G s) W= focus s.charge (Lattice.pull s.s (S.ratio.embed (Facet.pasta s)) W):=by
 let f:= (castX (reSweep G s)); rw [←mimeA S t s]; unfold flashA; change stir (xtra s.charge) f W= _; unfold focus; cases h:s.charge; rfl; rw [Cour.spin_c,Nacre.mores]; rfl
lemma boomP (i:Cell (Domain P B)): Pressure.toll (flashA (reSweep G s) V) i=Pressure.toll V (ζ i):=by
 rw [helve S t s]; have he:Pressure.toll (Lattice.pull s.s (S.ratio.embed (Facet.pasta s)) V) i = Pressure.toll V (ζ i) := Face.send_price V i s.s (S.ratio.embed (Facet.pasta s)) SU.group.chord SU.group.chord_inv fun u w=>SU.group.chord_conj w u
 unfold focus; split; exact (Rink.mint_b _ _).trans he; exact he -- tune
lemma stove_b(i:Cell (Domain P B)): touched i=actY T (touched (ζ i)):=by
 have hp:touched (ζ i)=(touched i).map (boxA T).toEmbedding:=by
    rw [←sit_k,stroll G S t,map_eq_image]; exact Work.H03.touched_send s.s _ i -- tune
 rw [hp,actY]; ext j; simp -- tune
lemma wish_b(i:Cell (Domain P B)) : i∈ inspectD (actY T X)↔ ζ i∈ inspectD X:=by simp only [inspectD,mem_filter,mem_univ,true_and]; nth_rw 1 [stove_b S t s i]; rw [lay_o]
lemma brine (C:ℝ): brushK (airport s A) (flashA (reSweep G s) V) C= actY T (brushK A V C):=by
 ext i; rw [actY,mem_map_equiv]; simp only [Equiv.symm_symm,brushK,mem_biUnion,mem_filter]; constructor
 · rintro ⟨x,⟨p,v⟩,h⟩; have he:(boxA T i)∈ touched (ζ x):=Finset.mem_map_equiv.mp ((stove_b S t s x) ▸ h : i∈ actY T _); exact ⟨ζ x,⟨(pay_l ..).mp p,(boomP S t s V x) ▸ v⟩,he⟩ -- tune
 rintro ⟨x,⟨p,v⟩,h⟩; obtain ⟨x,rfl⟩:=(shiftFaces s.s (S.ratio.embed (Facet.pasta s))).surjective x; exact ⟨x,⟨(pay_l ..).2 p, (boomP S t s V x).symm ▸ v⟩,(stove_b S t s x).symm ▸ (show i∈ actY T _ from Finset.mem_map_equiv.mpr h)⟩
lemma penV(i:Site (Domain P B)): i∈ inspected X ↔ i∈ X∨∃ q∈ inspectD X, i∈touched q:=by
 simp only [inspected, mem_union,mem_biUnion,mem_univ,true_and]; refine or_congr Iff.rfl (exists_congr ?_); intro i; split_ifs with v <;> simp [inspectD,v]
lemma lantern : inspected (actY (reSweep G s) X)=actY T (inspected X):=by
 ext i; rw [penV S t,show i∈actY T _↔_ from (show i∈actY T _↔ boxA T i ∈ inspected X from mem_map_equiv), penV S t,show i∈actY T _↔_ from (show i∈actY T X↔ boxA T i ∈ X from mem_map_equiv)]; refine or_congr Iff.rfl ?_
 constructor; · rintro ⟨j,v,h⟩; refine ⟨_,(wish_b S t s X j).mp v,?_⟩; rw [stove_b S t s] at h; exact Finset.mem_map_equiv.mp h
 rintro ⟨j,v,h⟩; obtain ⟨j,rfl⟩:=(shiftFaces s.s (S.ratio.embed (Facet.pasta s))).surjective j; refine ⟨j,(wish_b S t s X j).2 v,?_⟩; rw [stove_b S t s]; exact Finset.mem_map_equiv.mpr h
end YM.CF.Salt
