import YM.CF.BPress.Peel.Bore
/-! Reader ascent. radius.FRAME bells. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Peel
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Sugar.Crew Grid Env Bands Vesper Hazel Hazel.Letters Net
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace
variable {N: Side}{B:BandWidth}{A: Bands (More N) B}{R: Hangar (More N)}
open Palmer Contour
attribute [local instance] Gauge.frobInner
variable {H: Crew A} {t T S E P: Seal (BlockY A R)}{i : BlockY A R}{x y: Choir A R}
variable (g: Along x y S)
namespace Along
include g
lemma masks {r:ℕ}{b: BlockY A R}(p:Peel.stem b r⊆ S): Local (debts H x) r b ↔ Local (debts H y) r b:=by
 rw [←at_petal,←at_petal]; refine ⟨fun u=>?_,fun u=>?_⟩ <;> (obtain ⟨i,u,a⟩:=mem_biUnion.mp u; refine mem_biUnion.mpr ⟨i,?_ ,a⟩); exact (debtP g (p (stem_flip a))).1 u; exact (debtP g (p (stem_flip a))).2 u
abbrev fU(v:Choir A R):=House.read A R v
local notation "ξ"=> fU x
local notation "Ω"=> fU y
include g
lemma controls(v:A.Hcols)(p:own A R v∈ S): let u:=fU x;let U:=fU y; (v∈ u.1.1↔ v∈U.1.1) ∧ u.1.2 v = U.1.2 v ∧ u.2.1.1 v= U.2.1.1 v ∧ u.2.1.2 v= U.2.1.2 v:=by
 intro u U; have h:= g _ p; let k:= own A R v; let P:=packB R v.2; have he: gather A R (icon A R x) v=gather A R (icon A R y) v:= congrArg (fun z:Realm B N R=> z.1 P) h; exact ⟨ (beset_me ..).trans ((show (_=true)↔(_=true) from iff_of_eq (congrArg (fun z:Emblem=> z.1=true) he)).trans (beset_me ..|>.symm)), congrArg Prod.snd he, congrArg (fun z:Realm B N R=> z.2.1.1 P) h, congrArg (fun z:Realm B N R=> z.2.1.2 P) h⟩ -- tune
lemma horrors (v:Link (More N))(p:plan A R v.1∈ S): (fU x).2.2.1 v=(fU y).2.2.1 v:=congrArg (fun z:Realm B N R=> z.2.2.1 v) (g _ p)
lemma tags (v:Site (More N))(p:plan A R v∈ S): (fU x).2.2.2.1 v=(fU y).2.2.2.1 v:=congrArg (fun z:Realm B N R=> z.2.2.2.1 v) (g _ p)
lemma locks (v:Site (More N))(p:plan A R v∈ S): (fU x).2.2.2.2.1 v=(fU y).2.2.2.2.1 v:=congrArg (fun z:Realm B N R=> z.2.2.2.2.1 v) (g _ p)
lemma cylinders (v:Site N)(p:plan A R (node v)∈ S): (fU x).2.2.2.2.2 v=(fU y).2.2.2.2.2 v:=congrArg (fun z:Realm B N R=> z.2.2.2.2.2 v) (g _ p)
omit g in
abbrev reality (H:Crew A)(x:Choir A R):= bodyBase A H.y H.F (fU x).1.1 (fU x).2.1
def summerCo(H:Crew A): Prop:= Connect A H.F (H.P.reach H.y) --tune H.y field. R omitted
variable (p:summerCo H)(u:H.P.reach H.y≤ R.L.val)
include p u
lemma supreme (v:A.Hcols)(q:Peel.stem (own A R v) 1⊆ S): reality H x v=reality H y v:=by
 let U:= columnBall A v (H.P.reach H.y); have h(i:A.Hcols)(a:i∈ U): own A R i∈ S:= q (Peel.radial v i a u); exact body_reads (X:=A) p _ _ _ _ _ (fun i a=> (g.controls _ (h i a)).1) (fun i a=> (g.controls _ (h i a)).2.2.1) (g.controls _ (q (stem_home _ _))).2.2.2
lemma sky_tap (v:A.Air)(q:Peel.stem (own A R v.1) 1⊆S): H.skyio (fU x) v=H.skyio (fU y) v:=congrFun (g.supreme p u _ q) v.2
omit p u g in
private theorem elder (l:Link (More N))(x y: Bills A SU.E)(f:∀ i,edgeKey A l=some i→ x i=y i): angleBeg A H.y x l=angleBeg A H.y y l:= by unfold angleBeg; generalize hz: edgeKey A l=a at *; cases a with| none=> rfl| some a=> exact f a rfl
lemma stokes (l:Link (More N)){i:A.Index}(h:l∈inside (halo (Wealth.cloak B) (A.gap i)))(v: Peel.stem (plan A R l.1) 1⊆S) : H.port (fU x) l= H.port (fU y) l:=by
 have he(x:Choir A R): Mission A H.y (H.skyio (fU x)) (fU x).2.2.1 (H.port (fU x)):= marches ..; let b:= H.skyio (fU x); let c:= H.skyio (fU y); have hg : angleBeg A H.y b l= angleBeg A H.y c l:=by
    apply elder l _ _ (fun j hz=>?_)
    have k:Wealth.station A (l.1 0) i:= (zone_of_halo A i (Wealth.cloak B) l.1).1 (((inside_iff (halo (Wealth.cloak B) (A.gap i)) l).1 h).1); have hv:j.1=Locale.panel A l.1:=(key_housed A k hz).trans (Prod.ext (collar_ride A k le_rfl).symm rfl); exact g.sky_tap p u j (by rw [hv]; exact v)
 rw [(he x).narrates i l h, (he y).narrates i l h,anglePaid,anglePaid,g.horrors l (v (stem_home _ _)), show angleBeg A H.y (H.skyio (fU x)) l = angleBeg A H.y (H.skyio (fU y)) l from hg]
end Along
end YM.CF.BPress.Peel
