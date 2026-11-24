import GaugeFieldConstruction.Pantech
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry 
namespace Iona
variable {I J α β:Type}[Fintype I][LinearOrder I][Fintype α][Fintype β]
namespace Isle
variable {n:Side}(B:Isle I α β n)(p:Hub n)(S:List I)(s:Sect I)(σ:I→Seat n)(C:BudgetPoint)(U:Orbit n)(x:Key I)
abbrev gaugey (U:Orbit n)(i:α)(x:Key I):Cipher n:= if Disjoint (B.UV i) (flags C.threshold U.1) then carR x (B.W i) • B.F i U.1 else 0
def gaugeQ (x:Key I):Cipher n:=∑ i:α,B.gaugey C U i x
def κQ (i:β)(x:Key I):Cipher n:=carR x (B.B i) • B.Y i U
def heapQ (x:Key I):Cipher n:= hum (flags C.threshold U.1) B.U (fun i=>B.κQ U i x)
lemma run_Q (i:α):River (B.gaugey C U i):=by unfold gaugey; split; exact arc0 ..; exact zeroR _
lemma κQ_r(i:β):River (κQ B U i):= arc0 ..
lemma gaugeQ_r : River (B.gaugeQ C U):=(tip_bank _ _ (fun i _=> B.run_Q C U _)).1
lemma κr (V:Finset β): River (fun z=>∏ i∈ V,B.κQ U i z):=by
 induction V using Finset.induction_on with
 | empty=> simp_rw[prod_empty]; exact zeroR _
 | insert i V t h=> simp_rw[prod_insert t]; exact (B.κQ_r U _).mul_T h
lemma heapQ_r: River (B.heapQ C U):= (tip_bank _ _ (fun i _=>κr B U _)).1
local notation "Rι"=> Heart p (B.UV) s.reg.length
local notation "H"=> Legist p (B.UV) s.reg.length
local notation "Ω"=> flags C.threshold U.1
variable {S s}(t:x∈hill I)(p0:∀ i∈S,x i=0)(N:S.Nodup)(u:Night S s)
local notation "κ"=>s.reg.length
local notation "Kz"=> Fin s.reg.length
-- NOTE N means T need. σ=T.S. prove pointer requirement.
include t p0 N u
lemma crownZ {D X:Support (More n)}(w : X∩ flags C.threshold U.1 = D)(b:α)(j:Fin s.reg.length)(p:B.UV b⊆X) : lance (B.gaugey C U b) (boon s j) x=carR x (B.purseV S b) • B.noteV S (boon s j) b D U.1:=by
 have h:boon s j ∈s.reg:= List.get_mem ..
 have ht: (s.reg.flatten ++ s.pack).Nodup:=u.subs.nodup_iff.mpr N
 have hp(p):p∈s.reg → p.Sublist (s.reg.flatten++ s.pack):=fun k=> (show p.Sublist s.reg.flatten from (by simpa using (List.singleton_sublist.mpr k).flatten)).trans (List.sublist_append_left ..)
 have e: Disjoint (B.UV b) Ω↔Disjoint (B.UV b) D:=by
    constructor
    · intro v; rw[←w]; exact Disjoint.mono_right inter_subset_right v
    intro v; exact Finset.disjoint_left.mpr fun i hz hb=> Finset.disjoint_left.mp v hz (w ▸ mem_inter.mpr ⟨p hz,hb⟩)
 by_cases v:Disjoint (B.UV b) D
 · have hb:B.gaugey C U b=(fun z=>carR z (B.W b) • B.F b U.1):=funext fun z=> if_pos (e.mpr v)
   rw [hb]; rw [spar_z (B.W b) S _ _ ((hp _ h).nodup ht) (fun i t=> u.subs.mem_iff.mp ((hp _ h).subset t)) _ t p0]; unfold noteV; split; next k=> rw[if_pos ⟨k,v⟩]; rfl
   rw[if_neg (fun q=> ‹¬_› q.1), Pi.zero_apply,smul_zero]
 rw [show B.gaugey C U b=(fun _=>0) from (funext fun z=> if_neg (fun q=> v (e.mp q))),sil_Z (0:Cipher n) _ (u.duets _ h) x t]; unfold noteV; rw[if_neg (fun h=>v h.2),Pi.zero_apply,smul_zero]
lemma BPin (Z:Finset β):lance (fun z=>∏ i∈Z,B.κQ U i z) s.pack x= carR x (B.tressV S Z) • B.oracle S s Z U:=by
 have he:s.pack.Sublist (s.reg.flatten++ s.pack):= List.sublist_append_right ..
 rw [show (fun z=>∏ i∈Z,B.κQ U i z)=(fun z=> carR z (rosterF Z B.B) • (∏ i∈Z,B.Y i U)) from (funext fun z=> (roster_M Z B.B _ z).symm), spar_z _ S _ s.pack (he.nodup (u.subs.nodup_iff.mpr N)) (fun i t=> u.subs.mem_iff.mp (he.subset t)) _ t p0]
 unfold oracle tressV; split_ifs
 · rw [Finset.prod_apply]
 rw [Pi.zero_apply,smul_zero]
local notation "ηΦ" i:max=> rosterF univ (fun q:Fin s.reg.length=>B.purseV S (i q))
local notation "OPι" v:max D:max=> (∏ j:Fin s.reg.length,B.noteV S (boon s j) (v j) D)
local notation "Hι"=> Legist p B.UV s.reg.length
lemma RPin (v:Heart p B.UV s.reg.length)(X D:Support (More n))(m:(Hι v).val.2⊆ X)(e:X∩flags C.threshold U.1=D) : (∏ j: Kz,lance (B.gaugey C U (v.val j)) (boon s j) x) = carR x (ηΦ v.val) • (OPι v.val D) U.1:=by
 rw[roster_N,Finset.prod_apply]; rw[← Finset.prod_smul]; apply prod_congr rfl; intro j _; exact crownZ B C U x t p0 N u e _ j (fun i a=> m (mem_union_right _ (mem_biUnion.mpr ⟨j,mem_univ _,a⟩)))
-- support influence only
structure Isle.Speak (σ:I→Seat n):Prop where
    xy(i): B.F i ≠0→ poke_F σ (B.UV i) (B.W i).toFinset
    uv(i): B.Y i≠0→ poke_F σ (plateI B.U i) (B.B i).toFinset
variable (v':Isle.Speak B σ)(pK:poke_F σ p.val.2 S.toFinset)
include pK v'
lemma Leg_B : (s.reg.map (fun i=> lance (B.gaugeQ C U) i x)).prod = (∑ v: Heart p B.UV s.reg.length,∏ j:Kz,lance (B.gaugey C U (v.val j)) (boon s j) x):=by
 have W:(s.reg.map (fun i=> lance (B.gaugeQ C U) i x)).prod =∏ i:Kz,lance (B.gaugeQ C U) (boon s i) x:=by
    nth_rw 1 [←List.ofFn_get s.reg]; rw[List.map_ofFn,List.prod_ofFn]; rfl -- tune
 rw [W]; have e(i): lance (B.gaugeQ C U) i x=∑ j:α,lance (B.gaugey C U j) i x:=lnces_S _ _ (fun i _=>run_Q B C U _) _ x t
 simp_rw [e]; rw[Fintype.prod_sum]; let D(v:Fin s.reg.length→α):=(∏ j:Kz,lance (B.gaugey C U (v j)) (boon s j) x)
 let L:=LeadQ p.val.2 B.UV s.reg.length
 change ∑ v,D v=∑ v:↥L,D v.val; rw [← Finset.sum_subtype _ (p:=fun i=> i∈L) (fun i=> Iff.rfl)]
 symm; apply sum_subset (subset_univ _) (fun i t' g=>?_); by_contra h; apply g; refine mem_filter.mpr ⟨mem_univ _,fun j=>?_⟩
 let y:=i j; let V:= B.UV (i j); let T:=boon s j
 have hx:lance (B.gaugey C U y) T x≠0 :=fun e=> h (prod_eq_zero (mem_univ j) e)
 let W:=V∩flags C.threshold U.1
 rw[crownZ B C U x t p0 N u (show V∩_= W from rfl) y j (subset_refl _)] at hx
 unfold noteV at hx; split at hx; next Hp=>
    obtain ⟨b,hb⟩:= List.exists_mem_of_ne_nil T (u.duets T (List.get_mem ..)); have hS:b∈S:= u.subs.mem_iff.mp (List.mem_append_left _ (List.mem_flatten.mpr ⟨T,List.get_mem s.reg j,hb⟩)); have hy:b∈B.W y:= List.count_pos_iff.mp ((Hp.1 b hS).symm ▸ (List.count_pos_iff.mpr hb)); exact mem_filter.mpr ⟨mem_univ _, fun d=> Finset.disjoint_left.mp d (pK b (List.mem_toFinset.mpr hS)) (v'.xy _ (fun e=>hx (by rw[e,Pi.zero_apply,smul_zero])) b (List.mem_toFinset.mpr hy))⟩ -- disj orientation
 next e=> exact hx (by rw [Pi.zero_apply,smul_zero])|>.elim
lemma Cub_Z (r:Heart p B.UV s.reg.length)(J:Finset β): let P:= ashC (Hι r) B.U J; lance (fun z=>∏ i∈J,B.κQ U i z) s.pack x=(carR x (B.tressV S P) • B.oracle S s P U) * ∏ j∈J\P,B.κQ U j x:=by
 intro T; let R:=J\ T; let b(V:Finset β)(z):=∏ i∈V,B.κQ U i z
 have hw: T⊆ J:=filter_subset ..; rw[show (fun z=>∏ i∈J,B.κQ U i z)= b T * b R from (funext fun z=>by unfold b R; rw[Pi.mul_apply,mul_comm, Finset.prod_sdiff hw])] -- tune
 have hv(v:Key I)(i:I)(g:i∈s.pack)(z:ℂ): b R (update v i z)=b R v:=by
    apply prod_congr rfl; intro a p'
    by_cases h:B.Y a=0
    · simp[h,κQ]
    have e:i∉B.B a:=fun t=> ((mem_sdiff.mp p').2 ((ash_mem).2 ⟨(mem_sdiff.mp p').1,fun q=> Finset.disjoint_left.mp q (subset_union_left (pK i (List.mem_toFinset.mpr (u.subs.mem_iff.mp (List.mem_append_right _ g))))) ((v'.uv a h i) (List.mem_toFinset.mpr t))⟩))
    unfold κQ; apply congrArg (fun m:ℂ=>m • _); unfold carR; congr 1; exact List.map_congr_left (fun k p=>update_of_ne (fun v:k=i=>e (v ▸ p)) ..)
 rw [lances1 _ _ (κr B U T) (κr B U R) s.pack hv _ t]; exact congrArg (· * b R x) (BPin B U x t p0 N u T)
end Isle
end Iona
end YM.CF.Scree.Ing
end
