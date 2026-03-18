## Article/Case

javascript:void(inputStr=prompt("Article/Case Numbers (multiple allowed):","").trim(),caseIdsWithC=inputStr.match(/C\d{7,}/g)||[],pureCaseNums=inputStr.match(/\b\d{7,}\b/g)||[],allCaseNums=[...caseIdsWithC.map(c=>c.slice(1)),...pureCaseNums],uniqueCaseNums=[...new Set(allCaseNums)],articleIds=inputStr.match(/CS\d{4,6}/g)||[],numMatches=inputStr.match(/\b\d+\b/g)||[],monthAbbrs=['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'],validDigits=numMatches.filter(n=>([4,5,6].includes(n.length))&&!uniqueCaseNums.some(c=>c.includes(n))&&!monthAbbrs.some(m=>inputStr.includes(`${m} ${n.slice(0,2)}, ${n.slice(2)}`))&&!/^(20\d{2})$/.test(n)),validArticles=[...articleIds,...validDigits.map(n=>`CS${n}`)],uniqueArticles=[...new Set(validArticles)],uniqueArticles.forEach(a=>window.open(`https://www.ptc.com/en/support/article/${a}`)),uniqueCaseNums.forEach(c=>window.open(`https://support.ptc.com/apps/case_logger_viewer/auth/ssl/case=${c}`)),0);

## Issue

javascript:void(inputStr=prompt("Issue Number (multiple allowed):","").trim(),numMatches=inputStr.match(/\b\d{5,9}\b/g)||[],uniqueNums=[...new Set(numMatches)],uniqueNums.forEach(num=>{num!=="00000"&&window.open("https://codebeamer.com/cb/issue/"+encodeURIComponent(num),'_blank')}),0);

// Modified on 3/18/2026
