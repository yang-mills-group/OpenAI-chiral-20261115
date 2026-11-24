import YM.CF.BProof.Tape.Trip
/-! Tickets at Book. Preserve independent Pose/H matrices. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Tape
open Function Filter Fock Finset Branch Stint Align Wick Hearth Spin Tenant Lat Lattice Tulip Cube Fig
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{a b l r δ c v η:ℝ}{P: Ready j a b l r} (k:1≤v)(e:0<c)(x:0≤η)(g:η<1)
def earnV (P:Ready j a b l r)(δ c v:ℝ)(t:Pay):Prop:=∀ {N:Side}{F:Core j a b l r N}(h:Age P F δ), let p:=(h.beam c).mark; let X(q:InRoad F δ c):= F.upright (carried q); Earn t p p X∧ Earn t p p (fun i=> F.wind (carried i)) ∧ (∀ u, Earn t p p (cutX u)) ∧ Earn t p p (fun i=>F.θ (carried i) 1) ∧ ∀ (η:ℝ)(i:Key), let s:= (Tape.kiln h c v η).mark; Earn t (straw s) (straw s.reverseV) (divY (fun x=>view x i))
include k in
lemma purchaseV (P: Ready j a b l r)(δ c:ℝ):∃ y:Pay,earnV P δ c v y:=by
 obtain ⟨p,t⟩:= cutsBudget; obtain ⟨ν,E⟩:= sparkPrice v k; obtain ⟨q,Q⟩:= Core.earnsθ P; let f:=P.hP; let z:=(((Pay.simple.add f).mul f).mul f); let a:= f.lodge z; let b:=ν.lodge (q.lodge p); refine ⟨a.lodge b,?_⟩; intro N F h m X; let U:= h.beamSkid c; let L:= Hearth.kiln N P.hT δ
 have hk(v'):a.wide v' → (a.lodge b).wide v':= Pay.Wide (a.lodge_left b); have hz(v'):b.wide v'→(a.lodge b).wide v':= Pay.Wide (a.lodge_right b); have hu(v'):(q.lodge p).wide v'→(a.lodge b).wide v':=fun h=>hz _ (Pay.Wide (ν.lodge_right (q.lodge p)) h)
 exact ⟨(U.mark (L.mark (P.mat N h.minN F.M δ h.shelter))).change (hk _ (f.lodge_left z)), (U.mark (L.mark (F.earnsWind P h.minN h.shelter))).change (hk _ (f.lodge_right z)),fun i=>(U.mark (t N P.hT δ i)).change (hu _ (q.lodge_right p)),(U.mark (L.mark (Q F h.minN h.shelter))).change (hu _ (q.lodge_left p)),fun η i=>(E (η:=η) (c:=c) h i).change (hz _ (ν.lodge_left ..))⟩
include k e x g
lemma buys(P:Ready j a b l r)(δ:ℝ): ∃ p:Pay,∀ {N:Side}{F:Core j a b l r N}(h:Honor P F δ), Tickets p P δ c v η F h.1 :=by
 obtain ⟨a,H⟩:= purchaseV k P δ c; let z:= Spin.quota_p.le; obtain ⟨b,X⟩:= roll_cost z e g a; obtain ⟨s,T⟩:= Double.pullF e g z a a a a; obtain ⟨i,w,W⟩:= cash z e a a a a; obtain ⟨q,Q⟩:= lossCost z x g w a; let f:=b.lodge s; let y:=i.lodge q; refine ⟨y.lodge f,?_⟩; intro N F h
 let J:= h.1.beam c; let Y:=Loft F δ c v η; let G:= Tape.kiln h.1 c v η; let d(i:Y):=i.val.1
 obtain ⟨hA,hT,hQ,hL,L⟩:= H h.1; let A(u: InRoad F δ c):= F.upright (carried u); let A'(u:InRoad F δ c):=F.θ (carried u) 1; let U(u:InRoad F δ c):= F.wind (carried u); have ha(b:Raw _ _)(p)(t:Earn p J.mark J.mark b) :Earn p G.mark G.mark (fun x=>b (d x)):=gate h.1 t v η -- tune shadow hA
 have ht(T:Y): Ride (A (d T)) (U (d T)) (view T (true,false)) (view T (false,false)) (view T (true,true)) (view T (false,true)) (cutX true (d T)) (cutX false (d T)) c η:=T.property
 obtain ⟨hp,V⟩:= X G.cap (ha A _ hA) (ha U _ hT) (ha _ _ (hQ true)) (ha _ _ (hQ false)) (L η _) (L η _) (L η _) (L η _) ht; let C (x:Y):=view x (false,false) 1; have he:Earn a G.mark G.mark.reverseV C:=est (L η (false,false)) (⟨1,walk1⟩:Time)
 obtain ⟨hu,ζ⟩:= W J.cap hL (hQ true) (hQ false) hT (fun (i:InRoad F δ c)=> h.2 i.val.1) (fun i=>i.property); have hv(R:Y): Align.Twig (C R) (cutX true (d R)):= pairBy ..
 have hr: Earn q G.mark G.mark billR := Q G.cap (ha piF w ζ) he (fun i=>widthN' _ _ _ (d i).property (hv i) ((ht i).pores 1 walk1))
 have hs: Earn s (Double.dye G.mark).reverseV (Double.dye G.mark) driftW:= T G.cap (ha A' _ hL) (ha _ _ (hQ true)) (ha _ _ (hQ false)) he (fun i=>(ht i).frame)
 refine ⟨hu.change (Pay.Wide (y.lodge_left f) (i.lodge_left q)),hr.change (Pay.Wide (y.lodge_left f) (i.lodge_right q)),hp.change (Pay.Wide (y.lodge_right f) (b.lodge_left s)),hs.change (Pay.Wide (y.lodge_right f) (b.lodge_right s)),fun i=>⟨(V i).1,?_⟩⟩
 -- log identity
 let v:ℝ:=Pose (U (d i)) (A' (d i)) (cutX true (d i)) (cutX false (d i)); have hx (k:Y): rolled (A (d k)) (U (d k)) (view k (true,false)) (view k (false,false)) (view k (true,true)) (view k (false,true)) (cutX true (d k)) (cutX false (d k))=(labelR k).trace:= (V k).2
 unfold keyF lumpLog; simp only [poseQ,losses]; rw [←hx]; rfl
end YM.CF.BProof.Tape
