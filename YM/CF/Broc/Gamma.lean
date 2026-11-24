import YM.CF.Broc.Pocket
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Broc
open Function Filter Lattice Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Paige Phase Phase.Sample Brace Cube Peaks Tulip Rush Drapes
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
section
variable {Y Z T: Type*}[Fintype Y][DecidableEq Y]
lemma idemX (F:Branch.Field Y): Exceed F F id 1 1:=by refine ⟨fun {S} h=>h,fun {S} h=>by simp,fun i=>⟨{i},by simp,fun T h p=>⟨i,mem_singleton_self _,p⟩⟩⟩
-- linear price multiply, re, im
def rc : ℂ →L[ℝ] ℂ:= Complex.ofRealCLM.comp Complex.reCLM
def ri : ℂ→L[ℝ] ℂ:= Complex.ofRealCLM.comp Complex.imCLM
abbrev facet :ℂ→L[ℝ] ℂ:= (1/4:ℝ) • rc
abbrev folio' :ℂ →L[ℝ] ℂ:= (ContinuousLinearMap.mul ℝ ℂ Complex.I).comp ri
lemma facetP (x):facet x=↑(x.re/4):=by simp [facet,rc,Complex.real_smul]; ring
lemma folioT (x): folio' x= Complex.I*x.im:=rfl
end
variable {j:ℕ}{L: Side}{ho:Odd L.val}{T:Script Male}{Y:Pricing j L ho T}{B m r: Side}{e:ℝ}
variable (g:Grasp Y B e)(he:0<e)(G: Ratio (CSide m B) (CSide r B))(hc:G.count=L)(k:g.roundZ ≤(CSide m B).val)
lemma sector_f(U:sewA m r B) (p:SectorK g G U)(h:Fend _→SU.E):SectorK g G (frost G h U):=⟨solid _ _ p.glyph,joint_g G _ p.cap h,slow_g _ _ _ p.mist,slow_g _ _ _ p.loc⟩ -- tune
abbrev AcreZ (m r:Side)(g:Grasp Y B e)(G:Ratio (CSide m B) (CSide r B)) := {x:sewA m r B//SectorK g G x}
def aqua(x:AcreZ m r g G):Loom G Y.e :=⟨x.val,x.property.glyph⟩
def bunchS: Light (Fend (CSide r B)) (AcreZ m r g G) (Funds r B) where
 frame:=terr _
 rel T x y:= (weave G Y.e).rel T (aqua g G x) (aqua g G y)
 expands s t h x y p:= (weave G Y.e).expands s t h _ _ p
 dress h x:=⟨frost G h x.val,sector_f _ _ _ x.property h⟩
include hc k in
lemma traceH (u:AxisT)(A:Chop Male)(p: IndexB L u u A Y.A Y.C Y.e Y.N)(M:Male): Seat (bunchS g G) (fun i=> Matrix.trace (A M G (post i.val))) (Y.A/2) (quartzK Y.A Y.C):=by
 have ht := vertexP G (A:= A M G) (p M G hc (g.needed.trans k)) Y.rate Y.range
 have hh: 0≤ Y.C:=by obtain ⟨F,Q,h,w,U⟩:= p M G hc (g.needed.trans k); exact w.posP
 simpa only [one_mul,Function.comp_def,aqua] using (Seat.shop (b:=weave G Y.e) (c:=bunchS g G) (X:=fun i=> Matrix.trace (A M G (post i.val))) (idemX (terr _)) ht (aqua g G) (continuous_subtype_val.subtype_mk _) (qp _ _ hh) (show 0≤ Y.A/2 from (half_pos Y.rate).le) (by simp) (fun _ _ _ p=>p) (fun x y=>⟨y,rfl⟩))
-- use arbitrary support impulses for songs
omit k
lemma teak(g:Grasp Y B e)(k:g.roundZ≤ (CSide m B).val)(M:Male): Seat (pWorks m B e g.p) (fun x=> song m B (g.cost m M) x.val.1 x.val.2) (rateK g.a g.b/feeG (8*B.val)) (feeG (8*B.val)*chargeR' g.ea g.a g.w g.b):=by
  apply shoph g.topB g.baseY.1 _ (ratePos g.a g.positiveB g.b) _ _ (cargo g.sprawls g.guardV g.positiveB g.positiveW (m:=m*g.K) _ (g.clock.trans k) M)
  · unfold chargeR'; have he := rate_nonneg g.a _ g.b g.positiveW.le; positivity
  -- underscore knot coarse already inferred
end YM.CF.Broc
