"""Summarize focused diagnostic traces; no timing-based selection."""
import collections, csv, json, re, statistics, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent
CAPTURE=sys.argv[1] if len(sys.argv)>1 else 'sampled'
assert CAPTURE in ('sampled','history')
OUT=ROOT/'analysis'
OUT.mkdir(exist_ok=True)

def percentiles(values):
    v=sorted(values)
    return {'count':len(v),'mean':statistics.mean(v),'median':statistics.median(v),'p50':v[(len(v)-1)//2],'p95':v[max(0,(95*len(v)+99)//100-1)],'max':v[-1]} if v else {'count':0}

rows=[]
for label,path in [('original',ROOT/'original-bursts.json'),('baseline',ROOT/'baseline/report.json'),('sampled',ROOT/'sampled/report.json'),('history',ROOT/'history/bursts.json')]:
    for r in json.loads(path.read_text())['results']:
        n=r['messages'];spans=[s for w in r['workers'] for s in w['db_spans']]
        db={kind:sum(s['end_ns']-s['start_ns'] for s in spans if s['kind']==kind)/n/1e6 for kind in ('row_load','row_commit')}
        service=sum(x['metrics']['service_ns'] for x in r['observations'])/n/1e6
        rows.append(dict(collection=label,trial=r['trial'],arm=r['arm'],order=r['pair_order'],duration_ms=r['server_batch_ns']/1e6,mb_per_s=r['plaintext_bytes']*1000/r['server_batch_ns'],service_mean_ms=service,load_mean_ms=db['row_load'],commit_mean_ms=db['row_commit'],non_db_mean_ms=service-sum(db.values()),owner_cpu_ms=sum(w.get('scheduler_runtime_ns',0) for w in r['workers'])/1e6 if label!='original' else None,deadline_met=sum(x['metrics']['deadline_met'] for x in r['observations']),outputs_verified=r['outputs_verified']))
with (OUT/'trials.csv').open('w',newline='') as f:
    writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)

markers=[json.loads(line) for line in (ROOT/CAPTURE/'run.log').read_text().splitlines() if line.startswith('{')]
windows={}
for m in markers:
    key=(m['trial'],m['arm']);windows.setdefault(key,{})[m['event']]=m['monotonic_ns']
for key,w in windows.items():
    w['start']=w['begin']+50_000_000 # existing measurement_epoch's fixed lead; eprintln-to-epoch gap remains sub-ms.
    w.update(waits=collections.Counter(),active_waits=collections.Counter(),pids=set(),polls=0,poll_ms=[],client_cpu=collections.Counter(),pg_cpu=collections.Counter(),sync_ms=[],sync_intervals=[])

def window(stamp):
    return next(((key,w) for key,w in windows.items() if w['start']<=stamp<=w['end']),None)

for line in (ROOT/CAPTURE/'observer.jsonl').read_text().splitlines():
    sample=json.loads(line);entry=window(sample['begin_ns'])
    if not entry or sample['end_ns']>entry[1]['end']:continue
    key,w=entry;w['polls']+=1;w['poll_ms'].append((sample['end_ns']-sample['begin_ns'])/1e6)
    for pid,state,kind,event in sample['backends']:
        w['pids'].add(pid)
        name=f'{state}/{kind or "CPU-or-runnable"}/{event or "none"}'
        w['waits'][name]+=1
        if state=='active':w['active_waits'][name]+=1

pattern=re.compile(r'^\s*(.*?)\s+(\d+)/(\d+)\s+(\d+\.\d+):\s+(cpu-clock:u|syscalls:sys_(?:enter|exit)_(?:fdatasync|fsync)):\s+(.*)$')
perf_lines=(ROOT/CAPTURE/'perf-script.txt').read_text().splitlines()
bench_pids={int(m.group(2)) for line in perf_lines if (m:=pattern.match(line)) and m.group(1).startswith(('row-owner','cache-owner'))}
assert len(bench_pids)==1,bench_pids
bench_pid=bench_pids.pop()
parsed=0;unknown=0;pending={};unmatched=0
for line in perf_lines:
    if not line.strip():continue
    m=pattern.match(line)
    if not m:unknown+=1;continue
    parsed+=1
    comm,pid,tid,stamp,event,tail=m.groups();pid=int(pid);tid=int(tid)
    whole,frac=stamp.split('.');ns=int(whole)*10**9+int(frac.ljust(9,'0'))
    found=window(ns)
    if not found:continue
    key,w=found
    if event=='cpu-clock:u':
        symbol=tail.split(' ',1)[-1].rsplit(' (',1)[0].strip()
        # All benchmark threads share the sampled process ID; comm may be unavailable for threads created while disabled.
        if pid==bench_pid:w['client_cpu'][symbol]+=1
        if pid in w['pids']:w['pg_cpu'][symbol]+=1
    elif pid in w['pids']:
        syscall=event.rsplit('_',1)[1]
        if ':sys_enter_' in event:pending[(key,tid,syscall)]=ns
        else:
            start=pending.pop((key,tid,syscall),None)
            if start is None:unmatched+=1
            else:
                assert tail=='0x0',tail
                w['sync_ms'].append((ns-start)/1e6)
                w['sync_intervals'].append((start,ns))

assert unknown==0,unknown
summary={'parsed_events':parsed,'unmatched_sync_exits':unmatched,'unmatched_sync_enters':len(pending),'windows':[],'collections':{}}
for key,w in windows.items():
    trial,arm=key
    union=0;last_end=0
    for start,end in sorted(w['sync_intervals']):
        union+=max(0,end-max(start,last_end));last_end=max(last_end,end)
    summary['windows'].append({'trial':trial,'arm':arm,'window_ms':(w['end']-w['start'])/1e6,'backend_pids':sorted(w['pids']),'polls':w['polls'],'poll_duration_ms':percentiles(w['poll_ms']),'wait_observations':dict(w['waits']),'active_wait_observations':dict(w['active_waits']),'benchmark_user_cpu_samples':dict(w['client_cpu'].most_common()),'backend_user_cpu_samples':dict(w['pg_cpu'].most_common()),'backend_sync_ms':percentiles(w['sync_ms']),'backend_sync_total_ms':sum(w['sync_ms']),'backend_sync_union_ms':union/1e6})
for label in ('original','baseline','sampled','history'):
    subset=[r for r in rows if r['collection']==label]
    summary['collections'][label]={}
    for arm in ('row','cached_row'):
        rr=[r for r in subset if r['arm']==arm]
        summary['collections'][label][arm]={k:percentiles([r[k] for r in rr]) for k in ('duration_ms','mb_per_s','service_mean_ms','load_mean_ms','commit_mean_ms','non_db_mean_ms','owner_cpu_ms') if rr[0][k] is not None}
    ratios=[]
    for trial in sorted(set(r['trial'] for r in subset)):
        a={r['arm']:r for r in subset if r['trial']==trial}
        ratios.append(a['row']['duration_ms']/a['cached_row']['duration_ms'])
    summary['collections'][label]['paired_row_over_cached_duration']=dict(values=ratios,median=statistics.median(ratios),min=min(ratios),max=max(ratios))
(OUT/f'profile-{CAPTURE}.json').write_text(json.dumps(summary,indent=2)+'\n')
for label,data in summary['collections'].items():
    print(label,'paired',data['paired_row_over_cached_duration'])
    for arm in ('row','cached_row'):
        print(arm,{k:round(v['mean'],3) for k,v in data[arm].items()})
for arm in ('row','cached_row'):
    ww=[w for (trial,a),w in windows.items() if a==arm]
    waits=sum((w['active_waits'] for w in ww),collections.Counter())
    cpu=sum((w['client_cpu'] for w in ww),collections.Counter())
    syncs=[x for w in ww for x in w['sync_ms']]
    print('SAMPLED',arm,'activewaits',waits,'CPU',sum(cpu.values()),cpu.most_common(12),'SYNC',percentiles(syncs))
