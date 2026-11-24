import GaugeFieldConstruction.Gospels
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 55000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Neon
open Mew Vow Rive Roots
open scoped YM.CF.Mew
namespace CoeffArc
section
open Py.Riant Nor
variable {I:Type}[LinearOrder I][Fintype I]{N B:Side}{x h b a c:ℝ}{p:BudgetPoint}
variable (G:I→Oath.Zone (mid N B))(o:I→ Seat (mid N B))(C:I→ I→ℂ)(Yb:Key I→ Vow.Pax (mid N B))(Tp:Ids (mid N B))(t:0<h)
-- hold's transport per coefficient; wrapping widths.Drop to p. Use equality mini.Act.Job
variable (pp:p.power=2)(pt:p.order=6)(pu:p.B=radiusB x)(hr:∀ i y,River (fun z=>Yb z i y))(hp:∀ z∈hill I,Turf (Yb z)) (hv:∀ z∈hill I, ShelfK (SecW p t.le _) (Yb z) p.B 3 b)
include pp pt pu hv hp hr
lemma Wφ (l:List I): ShelfK (SecX (KeyUp p) t.le _) (fun i u=>tipI (fun z=>cast_E (Yb z) Tp i u) l) p.B 2 (ωCost x*b):=by
 apply RegT_p (KeyUp p) _ (fun z=>cast_E (Yb z) Tp) ?_ t (fun i u=> ripeC Tp pp pt pu (hp i u) t.le (hv i u)) l
 intro i v
 exact bScale _ (hr (lagE i) (v,Tp)) _ -- tune
include Tp
lemma Wχ (l:List I):ShelfK (SecW p t.le _) (fun i u=>tipI (fun z=>Yb z i u) l) p.B 2 (chi_f p.order*(ωCost x*b)):=by
 let V:Vow.Pax (mid N B):= fun i u=> tipI (fun z=>Yb z i u) l
 have he: Turf V:=fun i U x=> lace_C l (show Set.EqOn _ _ _ from fun z (t:z∈hill I)=> hp z t i U x) roots
 apply inbound Tp he _ pp
 have hh(i:Scree.Hub (mid N B))(y:Pane (mid N B)):cast_E V Tp i y= tipI (fun z=> cast_E (Yb z) Tp i y) l:=by
    let T:= lagE i; let c:ℂ:=bassH T; let F(z):= Yb z T (y,Tp); have ht(z):cast_E (Yb z) Tp i y = c • F z:= (Complex.coe_smul ..).symm -- tune
    simp_rw [ht]; rw [tip_C (hr _ _)]; exact (Complex.coe_smul ..).symm
 rw [funext fun i=>funext (hh i)]; exact Wφ Yb Tp t pp pt pu hr hp hv l -- tune
lemma W_v (l:List I)(pL:l.Nodup)(s:2 ≤ l.length):ShelfK (SecX (KeyUp p) t.le _) (fun i u=>tipI (fun z=>FacetE Yb (G_P G) Tp z i u) l) p.B (3/2) (ωCost x*b):=by
 simp_rw [pulse_I Yb (G_P G) Tp hr _ _ l pL s]; exact Shelf_roll _ (Wφ Yb Tp t pp pt pu hr hp hv l) (by norm_num)
omit pp pt pu hp hv
lemma D_Φ (i:I):Bus1 (FacetE Yb (G_P G) Tp) o C {i}=∑ j∈Roots.pipe_ζ o i,C j i • G_P G j:=by
 funext a u; unfold Bus1; rw [Dtip o C _ (growth_P Yb _ Tp hr a u)]; simp_rw [pulse_Z Yb _ Tp hr a u,Finset.sum_apply]; rfl
omit Tp
-- W_0 fees. heat formula $Yb=W-W(0)$ exact globally.Many expansions.Load
variable (W:Key I→ Vow.Pax (mid N B)) (w:∀ i,Yb i=W i-W 0)
omit hr
variable (X:Cusp (mid N B)){v:ℝ}(e:ℕ)
abbrev NQr (V:Key I)(X: Vow.Cusp (mid N B))(G:I→ Oath.Zone (mid N B)) := X+ Φstack (G_K G) V
lemma MixQr (i:Key I)(x)(p)(l): FlatQ (NQr i X G) x (p,l)= FlatQ X x (p,l) + Rep_C (fun j=> G_K G j x p l) i:=by unfold NQr FlatQ Φstack; simp_rw [Pi.add_apply,Finset.sum_apply]; rfl
lemma W_q (i) (r) (l) (s:List I)(x:I): tipI (fun z=> (NQr z X G) i r l) (x::s)=tipI (Rep_C fun j=>G_K G j i r l) (x::s):=by
 simp_rw [show ∀ z: Key I, NQr z X G i r l = _ from fun i'=>MixQr G X i' ..]; rw [tip_A (zeroR _) (rer_C _), Roots.proper, zero_add]
lemma Qro (i:Aura (mid N B))(D:Support (More (mid N B)))(J): River (fun z:Key I=>FlatQ (NQr z X G) i (D,J)):=by
 simp_rw [MixQr]; exact dub_V (zeroR _) (rer_C _)
section
variable (r:∀ i:I,HasCopper (e+1) (o i) p h (G_K G i) c)
include r
lemma access_q : Strain (SecQ p h _) o (fun z i=>FlatQ (NQr z X G) i):=by
 have ⟨hq,Z⟩:= FrameS p G o c r
 rintro i ⟨D,V⟩ s; refine ⟨Qro G X .., fun A v B' e H' =>?_⟩
 change X i D V+ Φstack (G_K G) A i D V= X i D V+ Φstack (G_K G) B' i D V; exact congrArg (_ + ·) (congrFun (hq i _ s.2 A v B' e H') V) -- tune
lemma access_Q1 (i:I) : ShelfK (SecQ p h _) (fun x y=>tipI (fun z=>FlatQ (NQr z X G) x y) [i]) p.B (3/2) c:=by
 let Q:=G_K G i; have hC: ShelfK (SecQ p h _) (FlatQ Q) p.B 3 c:=(Qbank p h Q).mp (HasCopper.till (r _)); refine Shelf_roll _ (Shelf_adapt _ ?_ hC) (by norm_num); rintro j ⟨p,H⟩ v; exact (Eq.symm ((W_q G X j p H [] i).trans (sTip ..))) -- tune
end
lemma Q_void (l:List I)(pL:l.Nodup)(s:2 ≤ l.length) : ShelfK (SecQ p h (mid N B)) (fun i x'=>tipI (fun z=>FlatQ (NQr z X G) i x') l) p.B a 0 :=by
 refine Shelf_zero _ ?_; rintro j ⟨D,u⟩ e; rcases l with _|⟨i,l⟩; · simp at s
 exact (W_q G X j D u l i).trans (far_P _ _ pL s)
include w
lemma tipsW(i:Aura (mid N B))(x':Orbit (mid N B))(j:I)(l:List I)(hx:River (fun z:Key I=> Yb z i x')): tipI (fun z=> W z i x') (j::l)= tipI (fun z=> Yb z i x') (j::l):=by
 have he: W=fun z=> Yb z+W 0:=funext fun z=>by rw [w z,sub_add_cancel]
 let F(i'):=(fun z:Key I=>Yb z i' x')
 have ht: (fun z=>W z i x')=fun z=> F i z + W 0 i x':=funext fun z=>congrFun (congrFun (congrFun he z) i) x'
 rw [ht,tip_A hx (zeroR _),Roots.proper,add_zero] -- order
variable (hu:∀ i,Hush o i.val (fun z=>Yb z i))
include hr hu
lemma Wstrain : Strain (SecW p t.le _) o W:=by
 intro i y _; let c:= fun z=> Yb z+W 0; have he:W=c:=funext fun z=>by unfold c; rw [w z,sub_add_cancel]
 change River (fun z=> W z i y)∧_; rw [he]; exact ⟨dub_V (hr _ _) (zeroR _),fun z v u w g=> congrArg (fun i':Copy (mid N B)=> (i'+ W 0 i) y) (hu _ z v u w g)⟩
include pp pt pu hv hp
lemma Wearn (l:List I)(h:l ≠ []):ShelfK (SecW p t.le _) (fun i y=> tipI (fun z=> W z i y) l) p.B (3/2) (chi_f p.order*(ωCost x*b)):=by
 rcases l with _|⟨i,l⟩; · simp at h
 simp_rw [show ∀ j y,tipI (fun z=>W z j y) (i::l)=_ from fun j y=>tipsW Yb W w j y i l (hr j y)]
 exact Shelf_roll _ (Wχ Yb (Classical.arbitrary _) t pp pt pu hr hp hv (i::l)) (by norm_num) -- note Tp not included use Class.
end
end CoeffArc
end Focus
end Pitching
end YM.CF.Py.Rate
end
