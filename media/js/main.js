document.addEventListener("DOMContentLoaded", function() {
  renderMathInElement(document.body, {
    // customised options
    // • auto-render specific keys, e.g.:
    delimiters: [
      {left: '$$', right: '$$', display: true},
      {left: '`', right: '`', display: false},
      {left: '\\(', right: '\\)', display: false},
      {left: '\\[', right: '\\]', display: true}
    ],
    // • rendering keys, e.g.:
    throwOnError : false
  });
});


function timeToSeconds(timeString) {
  // Split the time string into hours, minutes, and seconds
  const [hours, minutes, seconds] = timeString.split(':').map(Number);
  
  // Calculate the total time in seconds
  const totalTimeInSeconds = hours * 3600 + minutes * 60 + seconds;
  
  return totalTimeInSeconds;
}

// vid_helper("[[this]]", "[[youtubeid]]", "[[start]]", "[[end]]");
function vid_helper(elid, youtubeid, start, end) {
  asdfasdf
  
  mydiv = document.getElementById(elid);
  console.log("mydiv has element id: " + elid);
  myframe = mydiv.querySelector("iframe");
  console.log("myframe", myframe);
  
  var st = timeToSeconds(start);
  var et = timeToSeconds(end);

  console.log("vid_helper got youtubeid: " + youtubeid);
  var u = [
    `https://www.youtube.com/embed/`, youtubeid,
    `?autoplay=0`,
    `&enablejsapi=1`,
    `&start=` + st,
    `&end=` + et,
  ].join("");

  // 
  // myframe.src=u
  
}

function youtubeSeekTo(iframeId, startTime) {
  var player;
  function onYouTubeIframeAPIReady() {
    player = new YT.Player(iframeId, {
      events: {
        'onReady': onPlayerReady,
        'onStateChange': onPlayerStateChange
      }
    });
  }
  
  function onPlayerReady() {
    console.log("hey Im ready");
    player.seekTo(startTime);
    player.pauseVideo();
  }

  function onPlayerStateChange() {
    console.log("my state changed");
  }
}


var _unit = 1;
var _seq = 1;
var _page = 1;
var _def = 1;

function cur_def() {
  _def += 1;
  return ""+ _page + "." +_def + ".";
}

